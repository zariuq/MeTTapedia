import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Terms

/-!
# The reflective higher-order calculus on the step, for all closed processes

A store **represents** a closed process `P` (`RepresentsBy`) when its knowledge is solvable, every
solution gives each present row the same meaning (the knowledge is determinate on the rows), every
row means a closed canonical process, and the canonical primes of all rows, counted with
multiplicity, are the canonical bag of `P`. Parallel composition is the union of rows; the
equations of the source are carried by canonical forms inside rows and by the multiset of rows.

* `comm_effect`, `heat_effect`, `clear_effect`: what each admitted firing of the three schemas does
  to a represented store, for every admitted selection, fresh instance or not.
* `communication_sound`: every communication firing is a source reduction (no extra behaviour).
* `administration_silent`: every heating or clearing firing keeps the represented process.
* `administration_decreases`, `administration_bounded`: administrative firings strictly decrease
  the weight of the store, so a run of `k` of them from a represented store has `k` at most its
  weight.
* `heats_to_primes`: from every represented store, administrative firings reach a store whose
  rows are exactly the canonical primes.
* `communication_complete`: every source reduction is matched by administrative firings followed
  by one communication firing.
* `every_process_represented`, `represents_functional`, `represents_respects_equations`.
* `union_represents`: two stores with no common occurrence and no common rule instance represent,
  side by side, the parallel composition of what they represent.
* `barbs_agree`, `barbs_after_heating`: output barbs (on canonical channels) are read off one row of a
  store of primes, which every represented store reaches by silent firings.
* **`reflective_calculus_on_the_step`**: the representation is a weak bisimulation of unlabelled
  reductions, between the source reduction modulo the equations, on all closed processes, and the
  step with the rule set `Rules`, whose administrative firings are bounded by the weight; with
  `represents_functional` it is an operational correspondence. Its clauses relate reductions only:
  output barbs are related by the separate lemmas `barbs_agree` and `barbs_after_heating`, and a
  barbed bisimulation is not stated.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalize IsCanonical IsCanonicalList normalizeBagElements)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire Enabled)

/-! ## Rows and their primes -/

/-- A closed canonical process: what every row of a represented store means. -/
def Row (pattern : Pattern) : Prop :=
  RhoClosedTermWellSorted rhoProc pattern ∧ IsCanonical pattern

/-- The canonical primes of a pattern, with multiplicity. -/
def primes (pattern : Pattern) : Multiset Pattern :=
  (normalizeBagElements [canonicalize pattern] : Multiset Pattern)

theorem primes_process (process : RhoProcess) : primes process.1 = (fromProcess process).1 := rfl

theorem primes_canonicalize (pattern : Pattern) : primes (canonicalize pattern) = primes pattern := by
  unfold primes
  rw [Canonical.canonicalize_idempotent]

theorem primes_isPrime {pattern : Pattern} (row : Row pattern) :
    ∀ prime ∈ primes pattern, IsPrime prime :=
  fun prime member => (fromProcess ⟨pattern, row.1⟩).2 prime member

theorem primes_of_isPrime {pattern : Pattern} (prime : IsPrime pattern) :
    primes pattern = {pattern} := by
  unfold primes
  rw [Canonical.canonicalize_eq_of_isCanonical prime.2.1,
    Canonical.normalizeBagElements_eq_sort_bagContents,
    CanonicalStepperCompleteness.bagContents_eq_self
      (fun other member => by
        rw [List.mem_singleton] at member
        rw [member]
        exact prime.2.2.1)
      (fun other member => by
        rw [List.mem_singleton] at member
        rw [member]
        exact prime.2.2.2),
    ← Multiset.coe_singleton]
  exact Multiset.coe_eq_coe.mpr (Canonical.sortPatterns_perm [pattern]).symm

theorem primes_zero : primes zeroPattern = 0 := by
  have canonical : canonicalize zeroPattern = zeroPattern := rfl
  have contents : Canonical.bagContents [zeroPattern] = [] := by
    simp [Canonical.bagContents, Canonical.bagSplice, zeroPattern]
  unfold primes
  rw [canonical, Canonical.normalizeBagElements_eq_sort_bagContents, contents,
    List.perm_nil.mp (Canonical.sortPatterns_perm []).symm]
  exact Multiset.coe_nil

theorem row_ne_bvar {pattern : Pattern} (row : Row pattern) (index : Nat) :
    pattern ≠ .bvar index := by
  rintro rfl
  have safe := ((rhoClosedTermWellSorted_process_iff _).mp row.1).2
  simp [binderSafeAt] at safe

/-- A row is the null process, a canonical bag, or a prime. -/
theorem row_cases {pattern : Pattern} (row : Row pattern) :
    pattern = zeroPattern ∨ (∃ elements, pattern = .collection .hashBag elements none) ∨
      IsPrime pattern := by
  by_cases zero : pattern = zeroPattern
  · exact .inl zero
  by_cases bag : ∃ elements, pattern = .collection .hashBag elements none
  · exact .inr (.inl bag)
  · exact .inr (.inr ⟨row.1, row.2, zero, fun elements same => bag ⟨elements, same⟩⟩)

theorem isPrime_row {pattern : Pattern} (prime : IsPrime pattern) : Row pattern :=
  ⟨prime.1, prime.2.1⟩

/-- The members of a canonical bag row are primes, and it has at least two. -/
theorem bag_members {elements : List Pattern} (row : Row (.collection .hashBag elements none)) :
    2 ≤ elements.length ∧ ∀ member ∈ elements, IsPrime member := by
  have closed := (rhoClosedTermWellSorted_process_iff _).mp row.1
  have canonical := row.2
  simp only [IsCanonical] at canonical
  obtain ⟨length, _, shape, list⟩ := canonical
  refine ⟨length, fun member membership => ?_⟩
  obtain ⟨typed, safe⟩ :=
    CanonicalStepperCompleteness.closed_member closed.1 closed.2 membership
  exact ⟨(rhoClosedTermWellSorted_process_iff member).mpr ⟨typed, safe⟩,
    Canonical.isCanonicalList_mem list membership, (shape member membership).1,
    (shape member membership).2⟩

/-- A bag of primes, as a closed process. -/
def bagProcess (elements : List Pattern) (members : ∀ member ∈ elements, IsPrime member) :
    RhoProcess :=
  ofList elements (fun member membership => (members member membership).1)

theorem primes_bag {elements : List Pattern} (members : ∀ member ∈ elements, IsPrime member) :
    primes (.collection .hashBag elements none) = (elements : Multiset Pattern) :=
  fromProcess_ofList_primes elements members

/-- The canonical form of a bag of primes is a row with exactly those primes. -/
theorem canonical_bag_row {elements : List Pattern}
    (members : ∀ member ∈ elements, IsPrime member) :
    Row (canonicalize (.collection .hashBag elements none)) ∧
      primes (canonicalize (.collection .hashBag elements none)) = (elements : Multiset Pattern) := by
  refine ⟨⟨(RhoClosedTerm.canonicalize (bagProcess elements members)).2,
    Canonical.canonicalize_isCanonical _⟩, ?_⟩
  rw [primes_canonicalize]
  exact primes_bag members

/-- A canonical row is the canonical form of itself. -/
theorem primes_row_bag {elements : List Pattern} (row : Row (.collection .hashBag elements none)) :
    primes (.collection .hashBag elements none) = (elements : Multiset Pattern) :=
  primes_bag (bag_members row).2

/-- The administrative weight of a row: a bag weighs one more than its components, the null
process weighs one, and a prime weighs nothing. -/
def weight (pattern : Pattern) : Nat :=
  match bagElements pattern with
  | some elements => elements.length + 1
  | none => if pattern = zeroPattern then 1 else 0

theorem weight_zero : weight zeroPattern = 1 := rfl

theorem weight_bag (elements : List Pattern) :
    weight (.collection .hashBag elements none) = elements.length + 1 := rfl

theorem weight_of_isPrime {pattern : Pattern} (prime : IsPrime pattern) : weight pattern = 0 := by
  unfold weight
  cases found : bagElements pattern with
  | some elements => exact absurd (eq_of_bagElements found) (prime.2.2.2 elements)
  | none => simp [prime.2.2.1, zeroPattern]

theorem isPrime_of_weight {pattern : Pattern} (row : Row pattern) (light : weight pattern = 0) :
    IsPrime pattern := by
  rcases row_cases row with rfl | ⟨elements, rfl⟩ | prime
  · rw [weight_zero] at light
    exact absurd light one_ne_zero
  · rw [weight_bag] at light
    exact absurd light (Nat.succ_ne_zero _)
  · exact prime

theorem weight_le {pattern : Pattern} (row : Row pattern) :
    weight pattern ≤ Multiset.card (primes pattern) + 1 := by
  rcases row_cases row with rfl | ⟨elements, rfl⟩ | prime
  · rw [weight_zero]
    exact Nat.le_add_left 1 _
  · rw [primes_row_bag row, weight_bag, Multiset.coe_card]
  · rw [weight_of_isPrime prime]
    exact Nat.zero_le _

/-! ## Representation -/

/-- The primes of a set of occurrences under given meanings. -/
def inventory (present : Finset Occ) (meaning : Occ → Pattern) : Multiset Pattern :=
  ∑ occurrence ∈ present, primes (meaning occurrence)

/-- The total weight of a set of occurrences. -/
def storeWeight (present : Finset Occ) (meaning : Occ → Pattern) : Nat :=
  ∑ occurrence ∈ present, weight (meaning occurrence)

/-- **A store represents a closed process**, through the meanings of its rows. -/
structure RepresentsBy (C : Store) (P : RhoProcess) (meaning : Occ → Pattern) : Prop where
  consistent : ∃ g, Holds g C.equations
  determined : ∀ g, Holds g C.equations → ∀ o ∈ C.present, (label o).eval g = meaning o
  rows : ∀ o ∈ C.present, Row (meaning o)
  inventory_eq : inventory C.present meaning = (fromProcess P).1

/-- A store represents a closed process. -/
def Represents (C : Store) (P : RhoProcess) : Prop := ∃ meaning, RepresentsBy C P meaning

/-- Every row of the store is a prime. -/
def Heated (C : Store) (meaning : Occ → Pattern) : Prop := ∀ o ∈ C.present, IsPrime (meaning o)

theorem RepresentsBy.congr {C : Store} {P Q : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (same : (fromProcess P).1 = (fromProcess Q).1) :
    RepresentsBy C Q meaning :=
  ⟨represented.consistent, represented.determined, represented.rows,
    represented.inventory_eq.trans same⟩

theorem inventory_residue_prime {present : Finset Occ} {meaning : Occ → Pattern}
    (rows : ∀ o ∈ present, Row (meaning o)) (removed : Finset Occ) :
    ∀ prime ∈ inventory (present \ removed) meaning, IsPrime prime := by
  intro prime member
  obtain ⟨o, found, inPrimes⟩ := Multiset.mem_sum.mp member
  exact primes_isPrime (rows o (Finset.mem_sdiff.mp found).1) prime inPrimes

/-- The rows other than the removed ones, as a bag of primes. -/
def residue {present : Finset Occ} {meaning : Occ → Pattern}
    (rows : ∀ o ∈ present, Row (meaning o)) (removed : Finset Occ) : Bag :=
  ⟨inventory (present \ removed) meaning, inventory_residue_prime rows removed⟩

/-! ## Sums over a firing -/

theorem sum_split {M : Type} [AddCommMonoid M] {present taken : Finset Occ} (f : Occ → M)
    (sub : taken ⊆ present) :
    ∑ o ∈ present, f o = ∑ o ∈ present \ taken, f o + ∑ o ∈ taken, f o :=
  (Finset.sum_sdiff sub).symm

theorem sum_after {M : Type} [AddCommMonoid M] {present taken made : Finset Occ} {f f' : Occ → M}
    (fresh : Disjoint made present) (agree : ∀ o ∈ present, o ∉ taken → f' o = f o) :
    ∑ o ∈ (present \ taken) ∪ made, f' o = ∑ o ∈ present \ taken, f o + ∑ o ∈ made, f' o := by
  have apart : Disjoint (present \ taken) made :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
  rw [Finset.sum_union apart]
  congr 1
  exact Finset.sum_congr rfl fun o member =>
    agree o (Finset.mem_sdiff.mp member).1 (Finset.mem_sdiff.mp member).2

theorem holds_problem {g : Unknown → Pattern} {selection : Selection Occ}
    {rule : RuleInstance Tm} {C : Store} :
    Holds g (selection.problem label rule C) ↔
      Holds g C.equations ∧ Holds g (Selection.equations label rule.take selection.taken) ∧
        Holds g (Selection.equations label rule.read selection.read) ∧ Holds g rule.tell := by
  simp only [Selection.problem, holds_append, and_assoc]

theorem result_present {selection : Selection Occ} {rule : RuleInstance Tm} {C : Store} :
    (selection.result label rule C).present =
      (C.present \ selection.taken.toFinset) ∪ selection.made.toFinset := rfl

theorem result_equations {selection : Selection Occ} {rule : RuleInstance Tm} {C : Store} :
    (selection.result label rule C).equations = selection.problem label rule C := rfl

/-! ## Communication -/

theorem redex_val (rule : GroundComm) :
    rule.redex.1 = {input rule.inputChannel rule.body} + {output rule.outputChannel rule.payload} :=
  rfl

theorem redex_append (rule : GroundComm) (rest : Bag) :
    (append rule.redex rest).1 =
      input rule.inputChannel rule.body ::ₘ output rule.outputChannel rule.payload ::ₘ rest.1 := by
  rw [append_inventory, redex_val, Multiset.singleton_add, Multiset.cons_add,
    Multiset.singleton_add]

/-- **What a communication firing does.** For every admitted selection: the two taken rows are an
input and an output prime on the same channel, the process they belong to is that redex beside the
other rows, and the resulting store represents every process whose primes are the semantic
contractum beside the same other rows. -/
theorem comm_effect {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {index : Nat} {selection : Selection Occ}
    (valid : selection.Valid action label (comm index) C) :
    ∃ (o₁ o₂ : Occ) (rule : GroundComm) (meaning' : Occ → Pattern),
      selection.taken = [o₁, o₂] ∧
      meaning o₁ = input rule.inputChannel rule.body ∧
      meaning o₂ = output rule.outputChannel rule.payload ∧
      (fromProcess P).1 = rule.redex.1 + inventory (C.present \ {o₁, o₂}) meaning ∧
      storeWeight (selection.result label (comm index) C).present meaning' ≤
        storeWeight C.present meaning + Multiset.card rule.reactum.1 + 1 ∧
      ∀ Q : RhoProcess, (fromProcess Q).1 = rule.reactum.1 + inventory (C.present \ {o₁, o₂}) meaning →
        RepresentsBy (selection.result label (comm index) C) Q meaning' := by
  classical
  obtain ⟨o₁, o₂, taken⟩ := List.length_eq_two.mp valid.take_length.symm
  have readEmpty : selection.read = [] := List.eq_nil_of_length_eq_zero valid.read_length.symm
  have outputs : selection.made.map label =
      [Tm.react (unknown index .body) (unknown index .payload)] := valid.outputs
  obtain ⟨o₃, made, labelled⟩ := List.map_eq_singleton_iff.mp outputs
  have enabled := valid.occurrences
  have takenSub : ({o₁, o₂} : Finset Occ) ⊆ C.present := by
    have sub := enabled.taken_subset
    simpa [Selection.commit, taken] using sub
  have present₁ : o₁ ∈ C.present := takenSub (by simp)
  have present₂ : o₂ ∈ C.present := takenSub (by simp)
  have distinct : o₁ ≠ o₂ := by
    have nodup := valid.take_distinct
    rw [taken] at nodup
    simpa using nodup
  have fresh₃ : o₃ ∉ C.present := by
    have apart := enabled.fresh
    simp only [Selection.commit, made, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq] at apart
    exact Finset.disjoint_singleton_left.mp apart
  -- what a solution of the problem says
  have reads : ∀ g, Holds g (selection.problem label (comm index) C) →
      Holds g C.equations ∧
      input (unknown index .channel |>.eval g) (unknown index .body |>.eval g) = meaning o₁ ∧
      output (unknown index .channel |>.eval g) (unknown index .payload |>.eval g) = meaning o₂ := by
    intro g holds
    obtain ⟨old, takes, _, _⟩ := holds_problem.mp holds
    simp only [comm, taken, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true] at takes
    refine ⟨old, ?_, ?_⟩
    · exact takes.1.trans (represented.determined g old o₁ present₁)
    · exact takes.2.trans (represented.determined g old o₂ present₂)
  obtain ⟨g₀, solved₀⟩ := (consistent_iff _).mp valid.consistent
  obtain ⟨_, input₀, output₀⟩ := reads g₀ solved₀
  set channel := (unknown index .channel).eval g₀
  set body := (unknown index .body).eval g₀
  set payload := (unknown index .payload).eval g₀
  have rowInput := represented.rows o₁ present₁
  have rowOutput := represented.rows o₂ present₂
  have inputPrime : IsPrime (input channel body) := by
    rw [input₀]
    refine ⟨rowInput.1, rowInput.2, ?_, ?_⟩
    · rw [← input₀]; simp [input]
    · intro elements same; rw [← input₀] at same; simp [input] at same
  have outputPrime : IsPrime (output channel payload) := by
    rw [output₀]
    refine ⟨rowOutput.1, rowOutput.2, ?_, ?_⟩
    · rw [← output₀]; simp [output]
    · intro elements same; rw [← output₀] at same; simp [output] at same
  let rule : GroundComm := ⟨channel, channel, body, payload, inputPrime, outputPrime, rfl⟩
  let contractum := canonicalize rule.result.1
  let meaning' : Occ → Pattern := fun o => if o = o₃ then contractum else meaning o
  have contractumRow : Row contractum :=
    ⟨(RhoClosedTerm.canonicalize rule.result).2, Canonical.canonicalize_isCanonical _⟩
  refine ⟨o₁, o₂, rule, meaning', taken, input₀.symm, output₀.symm, ?_, ?_, ?_⟩
  · -- the redex and the other rows
    rw [← represented.inventory_eq]
    unfold inventory
    rw [sum_split _ takenSub, Finset.sum_pair distinct, ← input₀, ← output₀,
      primes_of_isPrime inputPrime, primes_of_isPrime outputPrime, add_comm]
    rfl
  · -- the weight after the firing
    unfold storeWeight
    rw [result_present, taken, made]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
    rw [sum_after (f := fun o => weight (meaning o)) (f' := fun o => weight (meaning' o))
      (Finset.disjoint_singleton_left.mpr fresh₃)
      (fun o oldMember _ => by
        have notNew : o ≠ o₃ := fun same => fresh₃ (same ▸ oldMember)
        simp only [meaning', notNew, if_false]),
      Finset.sum_singleton]
    have kept : ∑ o ∈ C.present \ {o₁, o₂}, weight (meaning o) ≤
        ∑ o ∈ C.present, weight (meaning o) :=
      Finset.sum_le_sum_of_subset Finset.sdiff_subset
    have madeWeight : weight (meaning' o₃) ≤ Multiset.card rule.reactum.1 + 1 := by
      have bound := weight_le contractumRow
      rw [primes_canonicalize] at bound
      simp only [meaning', if_true]
      exact bound
    exact (Nat.add_le_add kept madeWeight).trans (le_of_eq (Nat.add_assoc _ _ _).symm)
  · intro Q readsQ
    refine ⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩
    · -- determinacy
      intro g holds o member
      rw [result_present] at member
      rw [result_equations] at holds
      obtain ⟨old, inputG, outputG⟩ := reads g holds
      rcases Finset.mem_union.mp member with kept | new
      · have keptOld := Finset.mem_sdiff.mp kept
        have notNew : o ≠ o₃ := fun same => fresh₃ (same ▸ keptOld.1)
        simp only [meaning', notNew, if_false]
        exact represented.determined g old o keptOld.1
      · have isNew : o = o₃ := by simpa [made] using new
        subst isNew
        simp only [meaning', if_true]
        rw [labelled]
        have bodyG : (unknown index .body).eval g = body := by
          have same := inputG.trans input₀.symm
          simp only [input, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq,
            true_and, and_true] at same
          exact same.2
        have payloadG : (unknown index .payload).eval g = payload := by
          have same := outputG.trans output₀.symm
          simp only [output, Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at same
          exact same.2
        simp only [Tm.eval]
        rw [bodyG, payloadG]
        rfl
    · -- rows
      intro o member
      rw [result_present] at member
      rcases Finset.mem_union.mp member with kept | new
      · have keptOld := Finset.mem_sdiff.mp kept
        have notNew : o ≠ o₃ := fun same => fresh₃ (same ▸ keptOld.1)
        simp only [meaning', notNew, if_false]
        exact represented.rows o keptOld.1
      · have isNew : o = o₃ := by simpa [made] using new
        subst isNew
        simp only [meaning', if_true]
        exact contractumRow
    · -- inventory
      rw [readsQ]
      unfold inventory
      rw [result_present, taken, made]
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      rw [sum_after (f := fun o => primes (meaning o)) (f' := fun o => primes (meaning' o))
        (Finset.disjoint_singleton_left.mpr fresh₃)
        (fun o oldMember _ => by
          have notNew : o ≠ o₃ := fun same => fresh₃ (same ▸ oldMember)
          simp only [meaning', notNew, if_false])]
      rw [Finset.sum_singleton]
      simp only [meaning', if_true]
      rw [primes_canonicalize, add_comm]
      rfl

/-- **Every communication firing is a source reduction.** -/
theorem communication_sound {C C' : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (fires : Communicates C C') :
    ∃ (P' : RhoProcess) (meaning' : Occ → Pattern),
      rhoLanguageDefGSLT.Step P P' ∧ RepresentsBy C' P' meaning' := by
  obtain ⟨index, selection, valid, rfl⟩ := fires
  obtain ⟨o₁, o₂, rule, meaning', _, _, _, source, _, target⟩ := comm_effect represented valid
  let rest := residue represented.rows {o₁, o₂}
  let P' := toProcess (append rule.reactum rest)
  have readP' : (fromProcess P').1 = rule.reactum.1 + inventory (C.present \ {o₁, o₂}) meaning := by
    simp only [P', fromProcess_toProcess, append_inventory]
    rfl
  refine ⟨P', meaning', ?_, target P' readP'⟩
  apply (publicStep_iff P P').mpr
  refine ⟨rule, rest, ?_, by simp only [P', fromProcess_toProcess]⟩
  apply Subtype.ext
  rw [source, append_inventory]
  rfl

/-- **The cost of one communication.** From a store of primes, a communication firing is a source
reduction to some `P'` and leaves a store of weight at most the number of primes of `P'` plus one;
by `administration_bounded`, at most that many administrative firings can follow it. -/
theorem communication_cost {C C' : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (heated : Heated C meaning)
    (fires : Communicates C C') :
    ∃ (P' : RhoProcess) (meaning' : Occ → Pattern), rhoLanguageDefGSLT.Step P P' ∧
      RepresentsBy C' P' meaning' ∧
      storeWeight C'.present meaning' ≤ Multiset.card (fromProcess P').1 + 1 := by
  obtain ⟨index, selection, valid, rfl⟩ := fires
  obtain ⟨o₁, o₂, rule, meaning', _, _, _, source, weightBound, target⟩ :=
    comm_effect represented valid
  let rest := residue represented.rows {o₁, o₂}
  let P' := toProcess (append rule.reactum rest)
  have readP' : (fromProcess P').1 = rule.reactum.1 + inventory (C.present \ {o₁, o₂}) meaning := by
    simp only [P', fromProcess_toProcess, append_inventory]
    rfl
  have light : storeWeight C.present meaning = 0 :=
    Finset.sum_eq_zero fun o member => weight_of_isPrime (heated o member)
  refine ⟨P', meaning', ?_, target P' readP', ?_⟩
  · apply (publicStep_iff P P').mpr
    refine ⟨rule, rest, ?_, by simp only [P', fromProcess_toProcess]⟩
    apply Subtype.ext
    rw [source, append_inventory]
    rfl
  · rw [light, zero_add] at weightBound
    rw [readP', Multiset.card_add]
    omega

/-! ## Heating and clearing -/

/-- **What a heating firing does**: the taken row is a canonical bag; its first prime and the
canonical form of the rest are made; the represented process does not change. -/
theorem heat_effect {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {index : Nat} {selection : Selection Occ}
    (valid : selection.Valid action label (heat index) C) :
    ∃ meaning' : Occ → Pattern,
      RepresentsBy (selection.result label (heat index) C) P meaning' ∧
      storeWeight (selection.result label (heat index) C).present meaning' <
        storeWeight C.present meaning := by
  classical
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp valid.take_length.symm
  have outputs : selection.made.map label =
      [unknown index .first, Tm.rest (unknown index .others)] := valid.outputs
  obtain ⟨o₄, o₅, made⟩ : ∃ o₄ o₅, selection.made = [o₄, o₅] := by
    have lengths := congrArg List.length outputs
    simp only [List.length_map, List.length_cons, List.length_nil] at lengths
    exact List.length_eq_two.mp lengths
  have labelled₄ : label o₄ = unknown index .first := by
    rw [made] at outputs; simp only [List.map_cons, List.map_nil, List.cons.injEq] at outputs
    exact outputs.1
  have labelled₅ : label o₅ = Tm.rest (unknown index .others) := by
    rw [made] at outputs; simp only [List.map_cons, List.map_nil, List.cons.injEq] at outputs
    exact outputs.2.1
  have enabled := valid.occurrences
  have present : o ∈ C.present := by
    have sub := enabled.taken_subset
    simp only [Selection.commit, taken, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.singleton_subset_iff] at sub
    exact sub
  have distinct : o₄ ≠ o₅ := by
    have nodup := valid.output_distinct
    rw [made] at nodup
    simpa using nodup
  have freshMade : Disjoint ({o₄, o₅} : Finset Occ) C.present := by
    have apart := enabled.fresh
    simpa [Selection.commit, made] using apart
  have fresh₄ : o₄ ∉ C.present := fun member =>
    Finset.disjoint_left.mp freshMade (by simp) member
  have fresh₅ : o₅ ∉ C.present := fun member =>
    Finset.disjoint_left.mp freshMade (by simp) member
  have reads : ∀ g, Holds g (selection.problem label (heat index) C) →
      Holds g C.equations ∧
      consBag ((unknown index .first).eval g) ((unknown index .others).eval g) = meaning o := by
    intro g holds
    obtain ⟨old, takes, _, _⟩ := holds_problem.mp holds
    simp only [heat, taken, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true] at takes
    exact ⟨old, takes.trans (represented.determined g old o present)⟩
  obtain ⟨g₀, solved₀⟩ := (consistent_iff _).mp valid.consistent
  obtain ⟨_, split₀⟩ := reads g₀ solved₀
  have row := represented.rows o present
  -- the taken row is a bag
  obtain ⟨tail, othersShape, rowShape⟩ : ∃ tail,
      (unknown index .others).eval g₀ = .collection .hashBag tail none ∧
      meaning o = .collection .hashBag ((unknown index .first).eval g₀ :: tail) none := by
    unfold consBag at split₀
    cases found : bagElements ((unknown index .others).eval g₀) with
    | none =>
        rw [found] at split₀
        exact absurd split₀.symm (row_ne_bvar row 0)
    | some elements =>
        rw [found] at split₀
        exact ⟨elements, eq_of_bagElements found, split₀.symm⟩
  set first := (unknown index .first).eval g₀
  have bagRow : Row (.collection .hashBag (first :: tail) none) := rowShape ▸ row
  obtain ⟨length, members⟩ := bag_members bagRow
  have firstPrime : IsPrime first := members first (by simp)
  have tailPrimes : ∀ member ∈ tail, IsPrime member :=
    fun member membership => members member (List.mem_cons_of_mem _ membership)
  obtain ⟨restRow, restPrimes⟩ := canonical_bag_row tailPrimes
  let meaning' : Occ → Pattern := fun occurrence =>
    if occurrence = o₄ then first else
      if occurrence = o₅ then canonicalize (.collection .hashBag tail none) else meaning occurrence
  have keep : ∀ occurrence ∈ C.present, meaning' occurrence = meaning occurrence := by
    intro occurrence member
    have not₄ : occurrence ≠ o₄ := fun same => fresh₄ (same ▸ member)
    have not₅ : occurrence ≠ o₅ := fun same => fresh₅ (same ▸ member)
    simp only [meaning', not₄, not₅, if_false]
  have at₄ : meaning' o₄ = first := by simp [meaning']
  have at₅ : meaning' o₅ = canonicalize (.collection .hashBag tail none) := by
    simp [meaning', distinct.symm]
  have madeFinset : selection.made.toFinset = {o₄, o₅} := by
    rw [made]; simp
  have takenFinset : selection.taken.toFinset = {o} := by
    rw [taken]; simp
  refine ⟨meaning', ⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro g holds occurrence member
    rw [result_present, madeFinset, takenFinset] at member
    rw [result_equations] at holds
    obtain ⟨old, splitG⟩ := reads g holds
    rw [rowShape] at splitG
    obtain ⟨tailG, othersG, elementsG⟩ := consBag_eq_bag splitG
    simp only [List.cons.injEq] at elementsG
    rcases Finset.mem_union.mp member with kept | new
    · have keptOld := Finset.mem_sdiff.mp kept
      rw [keep occurrence keptOld.1]
      exact represented.determined g old occurrence keptOld.1
    · rcases Finset.mem_insert.mp new with rfl | isFive
      · rw [at₄, labelled₄]
        exact elementsG.1.symm
      · rw [Finset.mem_singleton] at isFive
        subst isFive
        rw [at₅, labelled₅]
        simp only [Tm.eval]
        rw [othersG, ← elementsG.2]
        rfl
  · intro occurrence member
    rw [result_present, madeFinset, takenFinset] at member
    rcases Finset.mem_union.mp member with kept | new
    · have keptOld := Finset.mem_sdiff.mp kept
      rw [keep occurrence keptOld.1]
      exact represented.rows occurrence keptOld.1
    · rcases Finset.mem_insert.mp new with rfl | isFive
      · rw [at₄]; exact isPrime_row firstPrime
      · rw [Finset.mem_singleton] at isFive
        subst isFive
        rw [at₅]; exact restRow
  · rw [← represented.inventory_eq]
    unfold inventory
    rw [result_present, madeFinset, takenFinset,
      sum_after (f := fun occurrence => primes (meaning occurrence))
        (f' := fun occurrence => primes (meaning' occurrence))
        (madeFinset ▸ freshMade)
        (fun occurrence member _ => by rw [keep occurrence member]),
      sum_split (fun occurrence => primes (meaning occurrence))
        (Finset.singleton_subset_iff.mpr present),
      Finset.sum_pair distinct, Finset.sum_singleton, at₄, at₅, restPrimes,
      primes_of_isPrime firstPrime, rowShape, primes_bag members]
    simp
  · unfold storeWeight
    rw [result_present, madeFinset, takenFinset,
      sum_after (f := fun occurrence => weight (meaning occurrence))
        (f' := fun occurrence => weight (meaning' occurrence))
        (madeFinset ▸ freshMade)
        (fun occurrence member _ => by rw [keep occurrence member]),
      sum_split (fun occurrence => weight (meaning occurrence))
        (Finset.singleton_subset_iff.mpr present),
      Finset.sum_pair distinct, Finset.sum_singleton]
    have w₄ : weight (meaning' o₄) = 0 := by
      rw [at₄]
      exact weight_of_isPrime firstPrime
    have w₅ : weight (meaning' o₅) ≤ tail.length + 1 := by
      rw [at₅]
      have bound := weight_le restRow
      rw [restPrimes, Multiset.coe_card] at bound
      exact bound
    have wo : weight (meaning o) = tail.length + 2 := by
      rw [rowShape, weight_bag]
      rfl
    simp only [w₄, wo]
    omega

/-- **What a clearing firing does**: the taken row is the null process. -/
theorem clear_effect {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {index : Nat} {selection : Selection Occ}
    (valid : selection.Valid action label (clear index) C) :
    RepresentsBy (selection.result label (clear index) C) P meaning ∧
      storeWeight (selection.result label (clear index) C).present meaning <
        storeWeight C.present meaning := by
  classical
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp valid.take_length.symm
  have outputs : selection.made.map label = [] := valid.outputs
  have made : selection.made = [] := List.map_eq_nil_iff.mp outputs
  have enabled := valid.occurrences
  have present : o ∈ C.present := by
    have sub := enabled.taken_subset
    simp only [Selection.commit, taken, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.singleton_subset_iff] at sub
    exact sub
  have reads : ∀ g, Holds g (selection.problem label (clear index) C) →
      Holds g C.equations ∧ zeroPattern = meaning o := by
    intro g holds
    obtain ⟨old, takes, _, _⟩ := holds_problem.mp holds
    simp only [clear, taken, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true] at takes
    exact ⟨old, takes.trans (represented.determined g old o present)⟩
  obtain ⟨g₀, solved₀⟩ := (consistent_iff _).mp valid.consistent
  obtain ⟨_, zero₀⟩ := reads g₀ solved₀
  have presentAfter : (selection.result label (clear index) C).present = C.present \ {o} := by
    rw [result_present, taken, made]
    simp
  refine ⟨⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro g holds occurrence member
    rw [presentAfter] at member
    rw [result_equations] at holds
    exact represented.determined g (reads g holds).1 occurrence (Finset.mem_sdiff.mp member).1
  · intro occurrence member
    rw [presentAfter] at member
    exact represented.rows occurrence (Finset.mem_sdiff.mp member).1
  · rw [presentAfter, ← represented.inventory_eq]
    unfold inventory
    rw [sum_split (fun occurrence => primes (meaning occurrence))
      (Finset.singleton_subset_iff.mpr present), Finset.sum_singleton, ← zero₀, primes_zero,
      add_zero]
  · rw [presentAfter]
    unfold storeWeight
    rw [sum_split (fun occurrence => weight (meaning occurrence))
      (Finset.singleton_subset_iff.mpr present) (present := C.present), Finset.sum_singleton,
      ← zero₀]
    have zeroWeight : weight zeroPattern = 1 := rfl
    rw [zeroWeight]
    omega

/-- **Administrative firings are silent and strictly decrease the weight.** -/
theorem administration_decreases {C C' : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (fires : Administers C C') :
    ∃ meaning' : Occ → Pattern, RepresentsBy C' P meaning' ∧
      storeWeight C'.present meaning' < storeWeight C.present meaning := by
  obtain ⟨index, ⟨selection, valid, rfl⟩ | ⟨selection, valid, rfl⟩⟩ := fires
  · exact heat_effect represented valid
  · exact ⟨meaning, clear_effect represented valid⟩

theorem administration_silent {C C' : Store} {P : RhoProcess}
    (represented : Represents C P) (fires : Administers C C') : Represents C' P := by
  obtain ⟨meaning, represented⟩ := represented
  obtain ⟨meaning', represented', _⟩ := administration_decreases represented fires
  exact ⟨meaning', represented'⟩

/-- Runs of exactly `k` administrative firings. -/
inductive AdministrativeRun : Nat → Store → Store → Prop
  | refl (C : Store) : AdministrativeRun 0 C C
  | head {k : Nat} {C D E : Store} : Administers C D → AdministrativeRun k D E →
      AdministrativeRun (k + 1) C E

/-- **Administrative firings are bounded**: a run of `k` of them from a represented store has `k`
at most the store's weight. -/
theorem administration_bounded {C E : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    {k : Nat} (represented : RepresentsBy C P meaning) (run : AdministrativeRun k C E) :
    k ≤ storeWeight C.present meaning := by
  induction run generalizing meaning with
  | refl => exact Nat.zero_le _
  | head fires _ earlier =>
      obtain ⟨meaning', represented', lighter⟩ := administration_decreases represented fires
      have bound := earlier represented'
      omega

/-! ## Existence: firings that the step admits -/

/-- The rule instances a store mentions. -/
def mentioned (C : Store) : Finset Nat :=
  storeIndices C.equations ∪ C.present.biUnion fun o => (label o).indices

theorem not_mem_label_indices {C : Store} {index : Nat} (fresh : index ∉ mentioned C)
    {o : Occ} (member : o ∈ C.present) : index ∉ (label o).indices := fun found =>
  fresh (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨o, member, found⟩))

theorem not_mem_storeIndices {C : Store} {index : Nat} (fresh : index ∉ mentioned C) :
    index ∉ storeIndices C.equations := fun found => fresh (Finset.mem_union_left _ found)

/-- A clearing firing exists at every null row. -/
theorem clear_exists {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {o : Occ} (member : o ∈ C.present)
    (zero : meaning o = zeroPattern) :
    ∃ C', Administers C C' := by
  classical
  obtain ⟨g, holds⟩ := represented.consistent
  refine ⟨_, 0, .inr ⟨⟨[o], [], []⟩, ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩⟩
  · simp
  · simp
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Selection.commit, member]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
  · apply (consistent_iff _).mpr
    refine ⟨g, holds_problem.mpr ⟨holds, ?_, by simp [Selection.equations], by simp [clear]⟩⟩
    simp only [clear, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true]
    rw [represented.determined g holds o member, zero]
    rfl
  · simp [clear]

/-- A heating firing exists at every bag row. -/
theorem heat_exists {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {o : Occ} (member : o ∈ C.present)
    {elements : List Pattern} (bag : meaning o = .collection .hashBag elements none) :
    ∃ C', Administers C C' := by
  classical
  obtain ⟨g, holds⟩ := represented.consistent
  have row := represented.rows o member
  rw [bag] at row
  obtain ⟨length, _⟩ := bag_members row
  obtain ⟨first, tail, rfl⟩ : ∃ first tail, elements = first :: tail := by
    cases elements with
    | nil => simp at length
    | cons first tail => exact ⟨first, tail, rfl⟩
  obtain ⟨index, fresh⟩ := Infinite.exists_notMem_finset (mentioned C)
  obtain ⟨o₄, fresh₄, labelled₄⟩ := IndexedOccurrences.supply C.present (unknown index .first)
  obtain ⟨o₅, fresh₅, labelled₅⟩ :=
    IndexedOccurrences.supply (insert o₄ C.present) (Tm.rest (unknown index .others))
  have distinct : o₄ ≠ o₅ := fun same => fresh₅ (same ▸ Finset.mem_insert_self o₄ C.present)
  have fresh₅' : o₅ ∉ C.present := fun found => fresh₅ (Finset.mem_insert_of_mem found)
  let values : Port → Pattern
    | .first => first
    | .others => .collection .hashBag tail none
    | _ => zeroPattern
  have labelled₄' : label o₄ = unknown index .first := labelled₄
  have labelled₅' : label o₅ = Tm.rest (unknown index .others) := labelled₅
  refine ⟨_, index, .inl ⟨⟨[o], [], [o₄, o₅]⟩, ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩, rfl⟩⟩
  · simp
  · simp [distinct]
  · simp only [List.map_cons, List.map_nil, heat]
    rw [labelled₄', labelled₅']
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Selection.commit, member]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit, fresh₄, fresh₅']
    · simp [Selection.commit]
  · apply (consistent_iff _).mpr
    refine ⟨extend g index values, holds_problem.mpr
      ⟨holds_extend_of_fresh holds (not_mem_storeIndices fresh) values,
        ?_, by simp [Selection.equations], by simp [heat]⟩⟩
    simp only [heat, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true]
    rw [eval_extend_of_fresh g values (not_mem_label_indices fresh member),
      represented.determined g holds o member, bag]
    simp only [Tm.eval, eval_unknown_extend]
    rfl
  · simp [heat]

/-- **Heating reaches primes**: from every represented store, administrative firings reach a
store that represents the same process and whose rows are all primes. -/
theorem heats_to_primes {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) :
    ∃ (C' : Store) (meaning' : Occ → Pattern), Relation.ReflTransGen Administers C C' ∧
      RepresentsBy C' P meaning' ∧ Heated C' meaning' := by
  classical
  induction hw : storeWeight C.present meaning using Nat.strong_induction_on
    generalizing C meaning with
  | _ w earlier =>
    by_cases heated : Heated C meaning
    · exact ⟨C, meaning, .refl, represented, heated⟩
    · simp only [Heated, not_forall] at heated
      obtain ⟨o, member, notPrime⟩ := heated
      obtain ⟨C₁, fires⟩ : ∃ C₁, Administers C C₁ := by
        rcases row_cases (represented.rows o member) with zero | ⟨elements, bag⟩ | prime
        · exact clear_exists represented member zero
        · exact heat_exists represented member bag
        · exact absurd prime notPrime
      obtain ⟨meaning₁, represented₁, lighter⟩ := administration_decreases represented fires
      obtain ⟨C', meaning', run, represented', heated'⟩ :=
        earlier _ (hw ▸ lighter) represented₁ rfl
      exact ⟨C', meaning', .head fires run, represented', heated'⟩

/-- On a store of primes, the inventory is the bag of row meanings. -/
theorem inventory_heated {C : Store} {meaning : Occ → Pattern} (heated : Heated C meaning) :
    inventory C.present meaning = C.present.val.map meaning := by
  unfold inventory
  rw [Finset.sum_congr rfl fun o member => primes_of_isPrime (heated o member),
    Finset.sum_eq_multiset_sum,
    show (fun o => ({meaning o} : Multiset Pattern)) =
      (fun pattern : Pattern => ({pattern} : Multiset Pattern)) ∘ meaning from rfl,
    ← Multiset.map_map, Multiset.sum_map_singleton]

theorem channel_canonical {channel body : Pattern} (prime : IsPrime (input channel body)) :
    canonicalize channel = channel :=
  Canonical.canonicalize_eq_of_isCanonical prime.2.1.1

theorem output_channel_canonical {channel payload : Pattern}
    (prime : IsPrime (output channel payload)) : canonicalize channel = channel :=
  Canonical.canonicalize_eq_of_isCanonical prime.2.1.1

/-- **Every source reduction is matched**: administrative firings, then one communication. -/
theorem communication_complete {C : Store} {P P' : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (step : rhoLanguageDefGSLT.Step P P') :
    ∃ (C₁ C₂ : Store) (meaning₂ : Occ → Pattern), Relation.ReflTransGen Administers C C₁ ∧
      Communicates C₁ C₂ ∧ RepresentsBy C₂ P' meaning₂ := by
  classical
  obtain ⟨C₁, meaning₁, run, represented₁, heated⟩ := heats_to_primes represented
  obtain ⟨rule, rest, source, target⟩ := (publicStep_iff P P').mp step
  have rows : C₁.present.val.map meaning₁ =
      input rule.inputChannel rule.body ::ₘ output rule.outputChannel rule.payload ::ₘ rest.1 := by
    rw [← inventory_heated heated, represented₁.inventory_eq, source, redex_append]
  -- the input row
  obtain ⟨o₁, member₁, at₁⟩ : ∃ o₁ ∈ C₁.present, meaning₁ o₁ = input rule.inputChannel rule.body := by
    have found : input rule.inputChannel rule.body ∈ C₁.present.val.map meaning₁ := by
      rw [rows]; exact Multiset.mem_cons_self _ _
    obtain ⟨o₁, member, same⟩ := Multiset.mem_map.mp found
    exact ⟨o₁, member, same⟩
  -- the output row, another occurrence
  obtain ⟨o₂, member₂, distinct, at₂⟩ : ∃ o₂ ∈ C₁.present, o₂ ≠ o₁ ∧
      meaning₁ o₂ = output rule.outputChannel rule.payload := by
    have split : C₁.present.val.map meaning₁ =
        meaning₁ o₁ ::ₘ (C₁.present.erase o₁).val.map meaning₁ := by
      rw [← Multiset.map_cons, ← Finset.insert_val_of_notMem (Finset.notMem_erase o₁ C₁.present),
        Finset.insert_erase member₁]
    rw [split, at₁] at rows
    have others := Multiset.cons_inj_right _ |>.mp rows
    have found : output rule.outputChannel rule.payload ∈ (C₁.present.erase o₁).val.map meaning₁ := by
      rw [others]; exact Multiset.mem_cons_self _ _
    obtain ⟨o₂, member, same⟩ := Multiset.mem_map.mp found
    have inErase := Finset.mem_erase.mp member
    exact ⟨o₂, inErase.2, inErase.1, same⟩
  have sameChannel : rule.inputChannel = rule.outputChannel := by
    have channels := rule.channels
    rwa [channel_canonical rule.inputPrime, output_channel_canonical rule.outputPrime] at channels
  -- a fresh instance and a fresh occurrence
  obtain ⟨index, fresh⟩ := Infinite.exists_notMem_finset (mentioned C₁)
  obtain ⟨o₃, fresh₃, labelled₃⟩ := IndexedOccurrences.supply C₁.present
    (Tm.react (unknown index .body) (unknown index .payload))
  obtain ⟨g, holds⟩ := represented₁.consistent
  let values : Port → Pattern
    | .channel => rule.inputChannel
    | .body => rule.body
    | .payload => rule.payload
    | _ => zeroPattern
  have labelled₃' : label o₃ = Tm.react (unknown index .body) (unknown index .payload) := labelled₃
  let selection : Selection Occ := ⟨[o₁, o₂], [], [o₃]⟩
  have valid : selection.Valid action label (comm index) C₁ := by
    refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [selection, distinct.symm]
    · simp [selection]
    · simp only [selection, List.map_cons, List.map_nil, comm]
      rw [labelled₃']
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro occurrence found
        simp only [Selection.commit, selection, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at found
        rcases found with rfl | rfl
        · exact member₁
        · exact member₂
      · simp [Selection.commit, selection]
      · simp [Selection.commit, selection]
      · simp [Selection.commit, selection, fresh₃]
      · simp [Selection.commit]
    · apply (consistent_iff _).mpr
      refine ⟨extend g index values, holds_problem.mpr
        ⟨holds_extend_of_fresh holds (not_mem_storeIndices fresh) values, ?_,
          by simp [selection, Selection.equations], by simp [comm]⟩⟩
      simp only [comm, selection, Selection.equations, List.zipWith_cons_cons,
        List.zipWith_nil_right, holds_cons, holds_nil, and_true]
      rw [eval_extend_of_fresh g values (not_mem_label_indices fresh member₁),
        eval_extend_of_fresh g values (not_mem_label_indices fresh member₂),
        represented₁.determined g holds o₁ member₁, represented₁.determined g holds o₂ member₂,
        at₁, at₂]
      simp only [Tm.eval, eval_unknown_extend]
      exact ⟨rfl, congrArg (fun channel => output channel rule.payload) sameChannel⟩
    · simp [comm]
  obtain ⟨o₁', o₂', rule', meaning₂, taken', at₁', at₂', source', _, target'⟩ :=
    comm_effect represented₁ valid
  have pair : o₁' = o₁ ∧ o₂' = o₂ := by
    have same : [o₁', o₂'] = [o₁, o₂] := taken'.symm
    simpa using same
  obtain ⟨rfl, rfl⟩ := pair
  have inputSame := at₁'.symm.trans at₁
  have outputSame := at₂'.symm.trans at₂
  simp only [input, output, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq,
    true_and, and_true] at inputSame outputSame
  have redexSame : rule'.redex.1 = rule.redex.1 := by
    simp only [GroundComm.redex, inputSame.1, inputSame.2, outputSame.1, outputSame.2]
  have reactumSame : rule'.reactum.1 = rule.reactum.1 := by
    simp only [GroundComm.reactum, GroundComm.result, ← primes_process, inputSame.2,
      outputSame.2]
  have restSame : inventory (C₁.present \ {o₁', o₂'}) meaning₁ = rest.1 := by
    have both : rule'.redex.1 + inventory (C₁.present \ {o₁', o₂'}) meaning₁ = rule.redex.1 + rest.1 := by
      rw [← source', source]
      rfl
    rw [redexSame] at both
    exact add_left_cancel both
  refine ⟨C₁, _, meaning₂, run, ⟨index, selection, valid, rfl⟩, target' P' ?_⟩
  rw [target, append_inventory, reactumSame, restSame]

/-! ## Parallel composition is the union of stores -/

/-- Two stores side by side: their knowledge and their rows. -/
def unionStore (C D : Store) : Store := ⟨C.equations ++ D.equations, C.present ∪ D.present⟩

/-- The parallel composition of two closed processes, through their canonical bags. -/
def parallel (P Q : RhoProcess) : RhoProcess := toProcess (append (fromProcess P) (fromProcess Q))

theorem parallel_inventory (P Q : RhoProcess) :
    (fromProcess (parallel P Q)).1 = (fromProcess P).1 + (fromProcess Q).1 := by
  simp only [parallel, fromProcess_toProcess, append_inventory]

/-- **Parallel composition is the union of stores.** Two stores that share no occurrence and no
rule instance represent, side by side, the parallel composition of what they represent. -/
theorem union_represents {C D : Store} {P Q : RhoProcess} {first second : Occ → Pattern}
    (left : RepresentsBy C P first) (right : RepresentsBy D Q second)
    (apart : Disjoint C.present D.present) (separate : Disjoint (mentioned C) (mentioned D)) :
    RepresentsBy (unionStore C D) (parallel P Q)
      (fun o => if o ∈ C.present then first o else second o) := by
  classical
  obtain ⟨g₁, holds₁⟩ := left.consistent
  obtain ⟨g₂, holds₂⟩ := right.consistent
  let g : Unknown → Pattern := fun u => if u.index ∈ mentioned C then g₁ u else g₂ u
  have onLeft : ∀ t : Tm, t.indices ⊆ mentioned C → t.eval g = t.eval g₁ := by
    intro t within
    apply Tm.eval_congr
    intro u member
    simp [g, within member]
  have onRight : ∀ t : Tm, t.indices ⊆ mentioned D → t.eval g = t.eval g₂ := by
    intro t within
    apply Tm.eval_congr
    intro u member
    have notLeft : u.index ∉ mentioned C := fun found =>
      Finset.disjoint_left.mp separate found (within member)
    simp [g, notLeft]
  have leftEquations : ∀ e ∈ C.equations, e.1.indices ⊆ mentioned C ∧ e.2.indices ⊆ mentioned C :=
    fun e member => ⟨(indices_subset_storeIndices member).1.trans Finset.subset_union_left,
      (indices_subset_storeIndices member).2.trans Finset.subset_union_left⟩
  have rightEquations : ∀ e ∈ D.equations, e.1.indices ⊆ mentioned D ∧ e.2.indices ⊆ mentioned D :=
    fun e member => ⟨(indices_subset_storeIndices member).1.trans Finset.subset_union_left,
      (indices_subset_storeIndices member).2.trans Finset.subset_union_left⟩
  refine ⟨⟨g, ?_⟩, ?_, ?_, ?_⟩
  · apply (holds_append _ _ _).mpr
    constructor
    · intro e member
      rw [onLeft e.1 (leftEquations e member).1, onLeft e.2 (leftEquations e member).2]
      exact holds₁ e member
    · intro e member
      rw [onRight e.1 (rightEquations e member).1, onRight e.2 (rightEquations e member).2]
      exact holds₂ e member
  · intro g' holds o member
    obtain ⟨holdsLeft, holdsRight⟩ := (holds_append _ _ _).mp holds
    rcases Finset.mem_union.mp member with inLeft | inRight
    · simp only [inLeft, if_true]
      exact left.determined g' holdsLeft o inLeft
    · have notLeft : o ∉ C.present := fun found => Finset.disjoint_left.mp apart found inRight
      simp only [notLeft, if_false]
      exact right.determined g' holdsRight o inRight
  · intro o member
    rcases Finset.mem_union.mp member with inLeft | inRight
    · simp only [inLeft, if_true]
      exact left.rows o inLeft
    · have notLeft : o ∉ C.present := fun found => Finset.disjoint_left.mp apart found inRight
      simp only [notLeft, if_false]
      exact right.rows o inRight
  · unfold inventory
    rw [show (unionStore C D).present = C.present ∪ D.present from rfl,
      Finset.sum_union apart, parallel_inventory, ← left.inventory_eq, ← right.inventory_eq]
    unfold inventory
    congr 1
    · exact Finset.sum_congr rfl fun o member => by simp only [member, if_true]
    · exact Finset.sum_congr rfl fun o member => by
        have notLeft : o ∉ C.present := fun found => Finset.disjoint_left.mp apart found member
        simp only [notLeft, if_false]

/-! ## Barbs -/

/-- **The output barb of the source** (§4, OUT-BARB, read on canonical forms): an output prime on
the canonical channel `channel`. -/
def Barb (P : RhoProcess) (channel : Pattern) : Prop :=
  ∃ payload, output channel payload ∈ (fromProcess P).1

/-- The output barb of a store: a row that is an output on the channel. -/
def StoreBarb (C : Store) (meaning : Occ → Pattern) (channel : Pattern) : Prop :=
  ∃ o ∈ C.present, ∃ payload, meaning o = output channel payload

/-- **On a store of primes, barbs are read off one row.** -/
theorem barbs_agree {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (heated : Heated C meaning) (channel : Pattern) :
    Barb P channel ↔ StoreBarb C meaning channel := by
  have rows : (fromProcess P).1 = C.present.val.map meaning := by
    rw [← represented.inventory_eq, inventory_heated heated]
  constructor
  · rintro ⟨payload, found⟩
    rw [rows] at found
    obtain ⟨o, member, same⟩ := Multiset.mem_map.mp found
    exact ⟨o, member, payload, same⟩
  · rintro ⟨o, member, payload, same⟩
    refine ⟨payload, ?_⟩
    rw [rows, ← same]
    exact Multiset.mem_map_of_mem meaning member

/-- **Weak barbs.** A represented process has a barb exactly when silent firings reach a store of
primes with that barb. -/
theorem barbs_after_heating {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) (channel : Pattern) :
    Barb P channel ↔ ∃ (C' : Store) (meaning' : Occ → Pattern),
      Relation.ReflTransGen Administers C C' ∧ RepresentsBy C' P meaning' ∧
        Heated C' meaning' ∧ StoreBarb C' meaning' channel := by
  constructor
  · intro barb
    obtain ⟨C', meaning', run, represented', heated'⟩ := heats_to_primes represented
    exact ⟨C', meaning', run, represented', heated',
      (barbs_agree represented' heated' channel).mp barb⟩
  · rintro ⟨C', meaning', _, represented', heated', barb⟩
    exact (barbs_agree represented' heated' channel).mpr barb

/-! ## The theorem -/

/-- The store with one row: the canonical form of a closed process. -/
def initialStore (P : RhoProcess) : Store := ⟨[], {(0, .lit (canonicalize P.1))}⟩

theorem initial_represents (P : RhoProcess) :
    RepresentsBy (initialStore P) P (fun _ => canonicalize P.1) := by
  refine ⟨⟨fun _ => zeroPattern, holds_nil _⟩, ?_, ?_, ?_⟩
  · intro g _ o member
    simp only [initialStore, Finset.mem_singleton] at member
    subst member
    rfl
  · intro _ _
    exact ⟨(RhoClosedTerm.canonicalize P).2, Canonical.canonicalize_isCanonical _⟩
  · unfold inventory
    simp only [initialStore, Finset.sum_singleton]
    rw [primes_canonicalize]
    rfl

theorem every_process_represented (P : RhoProcess) : Represents (initialStore P) P :=
  ⟨_, initial_represents P⟩

/-- A store represents one equation class: two processes it represents are equal modulo the
equations. -/
theorem represents_functional {C : Store} {P Q : RhoProcess} (first : Represents C P)
    (second : Represents C Q) : rhoProcessEquations.r P Q := by
  obtain ⟨meaning, first⟩ := first
  obtain ⟨meaning', second⟩ := second
  have same : inventory C.present meaning = inventory C.present meaning' := by
    unfold inventory
    obtain ⟨g, holds⟩ := first.consistent
    exact Finset.sum_congr rfl fun o member => by
      rw [← first.determined g holds o member, second.determined g holds o member]
  apply (fromProcess_eq_iff P Q).mp
  apply Subtype.ext
  rw [← first.inventory_eq, ← second.inventory_eq, same]

theorem represents_respects_equations {C : Store} {P Q : RhoProcess} (represented : Represents C P)
    (equal : rhoProcessEquations.r P Q) : Represents C Q := by
  obtain ⟨meaning, represented⟩ := represented
  exact ⟨meaning, represented.congr (congrArg Subtype.val ((fromProcess_eq_iff P Q).mpr equal))⟩

/-- **The reflective higher-order calculus on the step, for all closed processes.**

Through `Represents`, the step with the fixed rule set `Rules` (three schemas) is weakly bisimilar,
as an unlabelled reduction system, to the source reduction modulo the source equations, where
communication firings are the visible steps and heating and clearing firings are silent. The clauses
relate reductions only; barbs are related by `barbs_agree` and `barbs_after_heating`:

1. every closed process is represented;
2. every firing of the rule set is a communication or administrative;
3. an administrative firing keeps the represented process;
4. a communication firing is a source reduction (no extra behaviour);
5. every source reduction is matched by administrative firings followed by one communication;
6. a run of `k` administrative firings from a store represented through `meaning` has `k` at most
   `storeWeight` of that store. -/
theorem reflective_calculus_on_the_step :
    (∀ P : RhoProcess, ∃ C, Represents C P) ∧
    (∀ C C', (∃ rule, Rules rule ∧ Fires rule C C') ↔ Communicates C C' ∨ Administers C C') ∧
    (∀ {C C' : Store} {P : RhoProcess}, Represents C P → Administers C C' → Represents C' P) ∧
    (∀ {C C' : Store} {P : RhoProcess}, Represents C P → Communicates C C' →
      ∃ P', rhoLanguageDefGSLT.Step P P' ∧ Represents C' P') ∧
    (∀ {C : Store} {P P' : RhoProcess}, Represents C P → rhoLanguageDefGSLT.Step P P' →
      ∃ C₁ C₂, Relation.ReflTransGen Administers C C₁ ∧ Communicates C₁ C₂ ∧ Represents C₂ P') ∧
    (∀ {C E : Store} {P : RhoProcess} {meaning : Occ → Pattern} {k : Nat},
      RepresentsBy C P meaning → AdministrativeRun k C E → k ≤ storeWeight C.present meaning) := by
  refine ⟨fun P => ⟨_, every_process_represented P⟩, rules_fire_iff,
    fun represented fires => administration_silent represented fires, ?_, ?_,
    fun represented run => administration_bounded represented run⟩
  · intro C C' P represented fires
    obtain ⟨meaning, represented⟩ := represented
    obtain ⟨P', meaning', step, represented'⟩ := communication_sound represented fires
    exact ⟨P', step, meaning', represented'⟩
  · intro C P P' represented step
    obtain ⟨meaning, represented⟩ := represented
    obtain ⟨C₁, C₂, meaning₂, run, fires, represented₂⟩ := communication_complete represented step
    exact ⟨C₁, C₂, run, fires, meaning₂, represented₂⟩

#print axioms comm_effect
#print axioms communication_sound
#print axioms communication_cost
#print axioms heat_effect
#print axioms clear_effect
#print axioms administration_bounded
#print axioms heats_to_primes
#print axioms communication_complete
#print axioms represents_functional
#print axioms union_represents
#print axioms barbs_after_heating
#print axioms reflective_calculus_on_the_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus
