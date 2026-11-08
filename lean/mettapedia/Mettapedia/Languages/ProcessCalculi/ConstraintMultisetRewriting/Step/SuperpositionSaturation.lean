import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGuarded
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionCompleteness

/-!
# Ground saturation as firings of the guarded step

Ground clauses are stored as occurrences of the guarded one-frame step (`Superposition.guarded`),
each labelled by its clause. Ground clauses have nothing to substitute, so the step runs over the
**syntactic action** (`syntactic`): a read's equation says that the occurrence carries the clause
the firing names.

## Firings over labelled occurrences

`clauseFiring takes reads makes guard` takes, reads and makes occurrences, each with the label it
must carry, and guards `guard`. It is admitted exactly when the taken and read occurrences are
present with those labels, takes are distinct and apart from reads, made occurrences are fresh and
carry their labels, the knowledge is plain, and the guard holds (`clauseFiring_admits_iff`).

## Inferences are firings

`inferFiring side main made concl` **reads** its premises, **makes** the conclusion and **guards**
the side conditions of the inference. **Admission matches the side conditions exactly**
(`inferFiring_admits_iff`), and the clause set grows by the conclusion (`infer_clauses`).

## Simplifications take redundant clauses

`simplifyFiring` **takes** the simplified clause, **reads** its premises and **makes** its
replacements. The rules (`Simplification`): tautology deletion (a literal `s ≈ s`, or a literal
with its complement), subsumption by a strict sub-multiset, demodulation by a smaller unit equation,
and deletion of a literal `s ≉ s`. Each **removes only a clause that is redundant in the
Bachmair–Ganzinger sense with respect to the remaining set** (`simplify_takes_redundant`).

## Independence

* Two inferences with different made occurrences, both admitted, are **independent**
  (`infer_independent`): each is admitted after the other, so the two orders are trace equivalent
  runs (`infer_traceEquiv`), and a prover may interleave them.
* A simplification that takes a premise of an inference makes the two **dependent**
  (`simplify_takes_premise_dependent`): after it, the inference is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP
open Interface (Frames Transport)
open AnnotatedRuns (Firing)

universe uT uO

/-! ## The syntactic action -/

/-- **The syntactic action**: terms are compared as they are, and there is nothing to substitute. -/
def syntactic (T : Type uT) : SubstitutionAction T Unit where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := ()
  compose _ _ := ()
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

section Firings

variable {T : Type uT} {O : Type uO} [DecidableEq O] (label : O → T)

theorem syntactic_models_iff (σ : Unit) (store : EquationStore T) :
    (syntactic T).Models σ store ↔ ∀ e ∈ store, e.1 = e.2 :=
  Iff.rfl

/-- A configuration whose equations are all identities. -/
def Plain (C : Configuration T O) : Prop := ∀ e ∈ C.equations, e.1 = e.2

/-- **A firing over labelled occurrences**: it takes `takes`, reads `reads` and makes `makes`, each
occurrence with the label it must carry, and guards `guard`. -/
def clauseFiring (takes reads makes : List (O × T)) (guard : Prop) : GuardedFiring T Unit O :=
  ⟨⟨⟨takes.map Prod.snd, reads.map Prod.snd, [], [], makes.map Prod.snd⟩, [],
    ⟨takes.map Prod.fst, reads.map Prod.fst, makes.map Prod.fst⟩⟩, [fun _ => guard]⟩

omit [DecidableEq O] in
theorem pairs_eq : ∀ l : List (O × T),
    Selection.equations label (l.map Prod.snd) (l.map Prod.fst) = l.map fun p => (p.2, label p.1)
  | [] => rfl
  | p :: l => by
      show (p.2, label p.1) :: Selection.equations label (l.map Prod.snd) (l.map Prod.fst) = _
      rw [pairs_eq l]
      rfl

omit [DecidableEq O] in
/-- The information of a firing over labelled occurrences. -/
theorem clauseFiring_models_iff (C : Configuration T O) (takes reads makes : List (O × T)) (guard : Prop)
    (σ : Unit) :
    (syntactic T).Models σ ((clauseFiring takes reads makes guard).firing.selection.problem label
        (clauseFiring takes reads makes guard).firing.rule C) ↔
      Plain C ∧ ∀ p ∈ takes ++ reads, p.2 = label p.1 := by
  show (∀ e ∈ C.equations ++ Selection.equations label (takes.map Prod.snd) (takes.map Prod.fst) ++
      Selection.equations label (reads.map Prod.snd) (reads.map Prod.fst) ++ [], e.1 = e.2) ↔ _
  rw [pairs_eq, pairs_eq]
  constructor
  · intro all
    refine ⟨fun e member => all e (by simp [member]), fun p member => ?_⟩
    rcases List.mem_append.mp member with inT | inR
    · exact all (p.2, label p.1) (by simp only [List.append_nil, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨p, inT, rfl⟩))
    · exact all (p.2, label p.1) (by simp only [List.append_nil, List.mem_append, List.mem_map]; exact Or.inr ⟨p, inR, rfl⟩)
  · rintro ⟨plain, labels⟩ e member
    simp only [List.append_nil, List.mem_append, List.mem_map] at member
    rcases member with (inC | ⟨p, inT, rfl⟩) | ⟨p, inR, rfl⟩
    · exact plain e inC
    · exact labels p (List.mem_append_left _ inT)
    · exact labels p (List.mem_append_right _ inR)

/-- **Admission of a firing over labelled occurrences.** -/
theorem clauseFiring_admits_iff (C : Configuration T O) (takes reads makes : List (O × T)) (guard : Prop) :
    (guarded (syntactic T) label).Admits (s := C) (clauseFiring takes reads makes guard) ↔
      (takes.map Prod.fst).Nodup ∧ (makes.map Prod.fst).Nodup ∧
      (∀ p ∈ takes ++ reads, p.1 ∈ C.present ∧ label p.1 = p.2) ∧
      (∀ p ∈ takes, ∀ q ∈ reads, p.1 ≠ q.1) ∧
      (∀ p ∈ makes, p.1 ∉ C.present ∧ label p.1 = p.2) ∧ Plain C ∧ guard := by
  have models := clauseFiring_models_iff label C takes reads makes guard
  constructor
  · rintro ⟨⟨⟨takeDistinct, outputDistinct, -, -, outputs, occurrences, ⟨σ, solved⟩, -⟩, -⟩, asked⟩
    obtain ⟨plain, labels⟩ := (models σ).mp solved
    have madeLabels : ∀ p ∈ makes, label p.1 = p.2 := by
      have same : (makes.map Prod.fst).map label = makes.map Prod.snd := outputs
      rw [List.map_map] at same
      exact fun p member => (List.map_inj_left.mp same) p member
    refine ⟨takeDistinct, outputDistinct, fun p member => ⟨?_, (labels p member).symm⟩, ?_,
      fun p member => ⟨?_, madeLabels p member⟩, plain, asked σ solved _ (List.mem_singleton.mpr rfl)⟩
    · rcases List.mem_append.mp member with inT | inR
      · exact occurrences.taken_subset (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, inT, rfl⟩))
      · exact occurrences.kept_subset (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, inR, rfl⟩))
    · intro p inT q inR same
      exact Finset.disjoint_left.mp occurrences.apart
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, inT, rfl⟩))
        (same ▸ List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, inR, rfl⟩))
    · exact Finset.disjoint_left.mp occurrences.fresh
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, member, rfl⟩))
  · rintro ⟨takeDistinct, outputDistinct, present, apart, fresh, plain, holds⟩
    refine ⟨⟨⟨takeDistinct, outputDistinct, by simp [clauseFiring], by simp [clauseFiring], ?_,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨(), (models ()).mpr ⟨plain, fun p member => (present p member).2.symm⟩⟩,
      ?_⟩, ?_⟩, ?_⟩
    · show (makes.map Prod.fst).map label = makes.map Prod.snd
      rw [List.map_map]
      exact List.map_inj_left.mpr fun p member => (fresh p member).2
    · intro o member
      obtain ⟨p, inT, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact (present p (List.mem_append_left _ inT)).1
    · intro o member
      obtain ⟨p, inR, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact (present p (List.mem_append_right _ inR)).1
    · refine Finset.disjoint_left.mpr fun {o} inT inR => ?_
      obtain ⟨p, pT, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inT)
      obtain ⟨q, qR, same⟩ := List.mem_map.mp (List.mem_toFinset.mp inR)
      exact apart p pT q qR same.symm
    · refine Finset.disjoint_left.mpr fun {o} inM inC => ?_
      obtain ⟨p, pM, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inM)
      exact (fresh p pM).1 inC
    · intro query member
      cases member
    · intro check member
      cases member
    · intro query member
      cases member
    · intro σ _ g member
      simp only [clauseFiring, List.mem_singleton] at member
      subst member
      exact holds

/-- The result of a firing over labelled occurrences. -/
theorem clauseFiring_present (C : Configuration T O) (takes reads makes : List (O × T)) (guard : Prop) :
    ((clauseFiring takes reads makes guard).firing.result label C).present =
      (C.present \ (takes.map Prod.fst).toFinset) ∪ (makes.map Prod.fst).toFinset :=
  rfl

/-- **Admitted firings keep the knowledge plain.** -/
theorem clauseFiring_plain {C : Configuration T O} {takes reads makes : List (O × T)} {guard : Prop}
    (admitted : (guarded (syntactic T) label).Admits (s := C) (clauseFiring takes reads makes guard)) :
    Plain ((clauseFiring takes reads makes guard).firing.result label C) := by
  obtain ⟨⟨⟨-, -, -, -, -, -, ⟨σ, solved⟩, -⟩, -⟩, -⟩ := admitted
  exact solved

/-- The labels present in a configuration. -/
def clauses (C : Configuration T O) : Set T := {D | ∃ o ∈ C.present, label o = D}

end Firings

/-! ## Inferences as firings -/

section Inferences

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)] {O : Type uO} [DecidableEq O]
  (label : O → Clause (GroundTerm sig))

/-- **An inference as a firing**: it reads its premises, makes its conclusion and guards the
inference's side conditions. -/
def inferFiring (side : Option (O × Clause (GroundTerm sig))) (main : O × Clause (GroundTerm sig))
    (made : O) (concl : Clause (GroundTerm sig)) : GuardedFiring (Clause (GroundTerm sig)) Unit O :=
  clauseFiring [] (side.toList ++ [main]) [(made, concl)] (Inference (side.map Prod.snd) main.2 concl)

/-- **Admission of an inference firing matches the inference's side conditions exactly**: its
premises are present with their clauses, the made occurrence is fresh and carries the conclusion,
and the premises and conclusion form an inference of the calculus. -/
theorem inferFiring_admits_iff (C : Configuration (Clause (GroundTerm sig)) O)
    (side : Option (O × Clause (GroundTerm sig))) (main : O × Clause (GroundTerm sig)) (made : O)
    (concl : Clause (GroundTerm sig)) :
    (guarded (syntactic _) label).Admits (s := C) (inferFiring side main made concl) ↔
      (∀ p ∈ side.toList ++ [main], p.1 ∈ C.present ∧ label p.1 = p.2) ∧ made ∉ C.present ∧
        label made = concl ∧ Plain C ∧ Inference (side.map Prod.snd) main.2 concl := by
  rw [inferFiring, clauseFiring_admits_iff]
  constructor
  · rintro ⟨-, -, present, -, fresh, plain, inference⟩
    exact ⟨by simpa using present, (fresh _ (List.mem_singleton.mpr rfl)).1,
      (fresh _ (List.mem_singleton.mpr rfl)).2, plain, inference⟩
  · rintro ⟨present, fresh, made_label, plain, inference⟩
    refine ⟨List.nodup_nil, List.nodup_singleton _, by simpa using present, by simp, ?_, plain, inference⟩
    intro p member
    rw [List.mem_singleton.mp member]
    exact ⟨fresh, made_label⟩

/-- **An inference adds its conclusion to the clause set.** -/
theorem infer_clauses {C : Configuration (Clause (GroundTerm sig)) O}
    {side : Option (O × Clause (GroundTerm sig))} {main : O × Clause (GroundTerm sig)} {made : O}
    {concl : Clause (GroundTerm sig)}
    (admitted : (guarded (syntactic _) label).Admits (s := C) (inferFiring side main made concl)) :
    clauses label ((inferFiring side main made concl).firing.result label C) = clauses label C ∪ {concl} := by
  obtain ⟨-, -, made_label, -, -⟩ := (inferFiring_admits_iff label C side main made concl).mp admitted
  ext D
  simp only [clauses, inferFiring, clauseFiring_present, List.map_nil, List.toFinset_nil,
    Finset.sdiff_empty, List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
    List.toFinset_nil, Finset.notMem_empty, or_false, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨o, (inC | rfl), rfl⟩
    · exact Or.inl ⟨o, inC, rfl⟩
    · exact Or.inr made_label
  · rintro (⟨o, inC, rfl⟩ | rfl)
    · exact ⟨o, Or.inl inC, rfl⟩
    · exact ⟨made, Or.inr rfl, made_label⟩

/-! ## Simplifications -/

/-- **The simplification rules**: `Simplification C premises replacements`. -/
inductive Simplification :
    Clause (GroundTerm sig) → List (Clause (GroundTerm sig)) → List (Clause (GroundTerm sig)) → Prop
  /-- Tautology deletion: a literal `s ≈ s`. -/
  | tautology (C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig)) (member : L ∈ C)
      (positive : L.negative = false) (trivial : L.rhs = L.lhs) : Simplification C [] []
  /-- Tautology deletion: a literal together with its complement. -/
  | complementary (C : Clause (GroundTerm sig)) (L M : Lit (GroundTerm sig)) (inL : L ∈ C) (inM : M ∈ C)
      (positive : L.negative = false) (negative : M.negative = true) (sameLhs : M.lhs = L.lhs)
      (sameRhs : M.rhs = L.rhs) : Simplification C [] []
  /-- Subsumption by a strict sub-multiset. -/
  | subsumption (C D : Clause (GroundTerm sig)) (sub : D ≤ C) (proper : D ≠ C) : Simplification C [D] []
  /-- Demodulation: rewrite a side of a literal with a unit equation smaller than the clause. -/
  | demodulation {l r : GroundTerm sig} (C : Clause (GroundTerm sig)) (M : Lit (GroundTerm sig))
      (c : Ctx sig) (decreasing : r < l) (other : GroundTerm sig)
      (sides : (M.lhs = c.fill l ∧ M.rhs = other) ∨ (M.rhs = c.fill l ∧ M.lhs = other))
      (smaller : ClauseLT {Lit.pos l r decreasing.le} (M ::ₘ C)) :
      Simplification (M ::ₘ C) [{Lit.pos l r decreasing.le}] [Lit.make M.negative (c.fill r) other ::ₘ C]
  /-- Deletion of a literal `s ≉ s`. -/
  | deleteFalse (C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig)) (negative : L.negative = true)
      (trivial : L.rhs = L.lhs) : Simplification (L ::ₘ C) [] [C]

variable [GroundSimplification sig]

/-- **A simplified clause is redundant**: its premises and replacements are smaller, and entail it. -/
theorem Simplification.redundant {C : Clause (GroundTerm sig)} {premises replacements : List (Clause (GroundTerm sig))}
    (simplification : Simplification C premises replacements) :
    (∀ D ∈ premises ++ replacements, ClauseLT D C) ∧
      Entails {D | D ∈ premises ∨ D ∈ replacements} C := by
  cases simplification with
  | tautology C L member positive trivial =>
      refine ⟨fun D member => by simp at member, fun I _ => ⟨L, member, ?_⟩⟩
      rw [Lit.holds_of_positive positive, trivial]
      exact I.equivalence.refl _
  | complementary C L M inL inM positive negative sameLhs sameRhs =>
      refine ⟨fun D member => by simp at member, fun I _ => ?_⟩
      by_cases related : I.rel L.lhs L.rhs
      · exact ⟨L, inL, (Lit.holds_of_positive positive).mpr related⟩
      · refine ⟨M, inM, (Lit.holds_of_negative negative).mpr ?_⟩
        rwa [sameLhs, sameRhs]
  | subsumption C D sub proper =>
      refine ⟨fun E member => ?_, fun I holds => models_of_le sub (holds D (Or.inl (List.mem_singleton.mpr rfl)))⟩
      simp only [List.append_nil, List.mem_singleton] at member
      rw [member]
      exact clauseLT_of_lt sub proper
  | @demodulation l r C M c decreasing other sides smaller =>
      have below : Lit.make M.negative (c.fill r) other < M := by
        have step := c.fill_lt_fill decreasing
        rcases sides with ⟨atL, atR⟩ | ⟨atR, atL⟩
        · rcases (atR ▸ M.oriented : other ≤ M.lhs).lt_or_eq with lt | same
          · apply Lit.lt_of_lhs_lt
            rw [Lit.make_lhs]
            exact max_lt (step.trans_eq atL.symm) lt
          · have rOther : c.fill r < other := step.trans_eq (atL.symm.trans same.symm)
            refine Lit.lt_iff.mpr (Or.inr ⟨?_, Or.inr ⟨rfl, ?_⟩⟩)
            · show max (c.fill r) other = M.lhs
              rw [max_eq_right rOther.le, same]
            · show min (c.fill r) other < M.rhs
              rw [min_eq_left rOther.le, atR]
              exact rOther
        · refine Lit.lt_iff.mpr (Or.inr ⟨?_, Or.inr ⟨rfl, ?_⟩⟩)
          · show max (c.fill r) other = M.lhs
            rw [max_eq_right ((step.trans_eq atR.symm).le.trans (atL ▸ M.oriented)), atL]
          · show min (c.fill r) other < M.rhs
            rw [min_eq_left ((step.trans_eq atR.symm).le.trans (atL ▸ M.oriented)), atR]
            exact step
      refine ⟨fun D member => ?_, fun I holds => ?_⟩
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact smaller
        · have step := dm_replace C {Lit.make M.negative (c.fill r) other} M
            (fun y member => by rw [Multiset.mem_singleton.mp member]; exact below)
          rwa [add_comm, Multiset.singleton_add] at step
      · have unit := holds _ (Or.inl (List.mem_singleton.mpr rfl))
        obtain ⟨N, inN, ruleHolds⟩ := unit
        rw [Multiset.mem_singleton.mp inN, Lit.holds_of_positive rfl] at ruleHolds
        have down : I.rel (c.fill l) (c.fill r) := I.compatible c ruleHolds
        have replaced := holds _ (Or.inr (List.mem_singleton.mpr rfl))
        have symm : ∀ a b, I.rel a b → I.rel b a := fun _ _ h => I.equivalence.symm h
        rcases models_cons.mp replaced with made | rest
        · refine models_cons.mpr (Or.inl ?_)
          rw [Lit.holds_make symm] at made
          have sidesIff : I.rel M.lhs M.rhs ↔ I.rel (c.fill r) other := by
            rcases sides with ⟨atL, atR⟩ | ⟨atR, atL⟩
            · rw [atL, atR]
              exact ⟨fun h => I.equivalence.trans (symm _ _ down) h, fun h => I.equivalence.trans down h⟩
            · rw [atL, atR]
              exact ⟨fun h => symm _ _ (I.equivalence.trans h down),
                fun h => I.equivalence.trans (symm _ _ h) (symm _ _ down)⟩
          cases sign : M.negative
          · rw [sign] at made
            exact (Lit.holds_of_positive sign).mpr (sidesIff.mpr made)
          · rw [sign] at made
            exact (Lit.holds_of_negative sign).mpr fun h => made (sidesIff.mp h)
        · exact models_cons.mpr (Or.inr rest)
  | deleteFalse C L negative trivial =>
      refine ⟨fun D member => ?_, fun I holds => models_cons.mpr (Or.inr (holds C (Or.inr (List.mem_singleton.mpr rfl))))⟩
      simp only [List.nil_append, List.mem_singleton] at member
      rw [member]
      exact clauseLT_cons C L

/-- **A simplification as a firing**: it takes the simplified clause, reads its premises and makes its
replacements, guarded by the simplification rule. -/
def simplifyFiring (taken : O × Clause (GroundTerm sig)) (reads makes : List (O × Clause (GroundTerm sig))) :
    GuardedFiring (Clause (GroundTerm sig)) Unit O :=
  clauseFiring [taken] reads makes (Simplification taken.2 (reads.map Prod.snd) (makes.map Prod.snd))

/-- **A simplification firing takes only a redundant clause**: after it, the taken occurrence is gone,
and its clause is redundant (Bachmair–Ganzinger) with respect to the clauses that remain. -/
theorem simplify_takes_redundant {C : Configuration (Clause (GroundTerm sig)) O}
    {taken : O × Clause (GroundTerm sig)} {reads makes : List (O × Clause (GroundTerm sig))}
    (admitted : (guarded (syntactic _) label).Admits (s := C) (simplifyFiring taken reads makes)) :
    taken.1 ∉ ((simplifyFiring taken reads makes).firing.result label C).present ∧
      Redundant (clauses label ((simplifyFiring taken reads makes).firing.result label C)) taken.2 := by
  obtain ⟨-, -, present, apart, fresh, -, simplification⟩ :=
    (clauseFiring_admits_iff label C [taken] reads makes _).mp admitted
  have after := clauseFiring_present label C [taken] reads makes
    (Simplification taken.2 (reads.map Prod.snd) (makes.map Prod.snd))
  obtain ⟨smaller, entails⟩ := simplification.redundant
  refine ⟨?_, ?_⟩
  · show taken.1 ∉ (C.present \ ([taken].map Prod.fst).toFinset) ∪ (makes.map Prod.fst).toFinset
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, false_or,
      List.mem_toFinset, List.mem_map, not_exists, not_and]
    intro p member same
    exact (fresh p member).1 (same ▸ (present taken (List.mem_cons_self)).1)
  · refine entails.mono fun D member => ⟨?_, smaller D ?_⟩
    · rcases member with inReads | inMakes
      · obtain ⟨q, qR, rfl⟩ := List.mem_map.mp inReads
        refine ⟨q.1, ?_, (present q (List.mem_cons_of_mem _ qR)).2⟩
        show q.1 ∈ (C.present \ ([taken].map Prod.fst).toFinset) ∪ (makes.map Prod.fst).toFinset
        refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(present q (List.mem_cons_of_mem _ qR)).1, ?_⟩)
        simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_singleton]
        exact fun same => apart taken (List.mem_cons_self) q qR same.symm
      · obtain ⟨p, pM, rfl⟩ := List.mem_map.mp inMakes
        refine ⟨p.1, ?_, (fresh p pM).2⟩
        show p.1 ∈ (C.present \ ([taken].map Prod.fst).toFinset) ∪ (makes.map Prod.fst).toFinset
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, pM, rfl⟩))
    · rcases member with inReads | inMakes
      · exact List.mem_append_left _ inReads
      · exact List.mem_append_right _ inMakes

/-! ## Independence -/

omit [GroundSimplification sig] in
/-- After an admitted inference, another inference with a different made occurrence that was admitted
is still admitted. -/
theorem infer_after {C : Configuration (Clause (GroundTerm sig)) O}
    {side₁ side₂ : Option (O × Clause (GroundTerm sig))} {main₁ main₂ : O × Clause (GroundTerm sig)}
    {made₁ made₂ : O} {concl₁ concl₂ : Clause (GroundTerm sig)} (apart : made₁ ≠ made₂)
    (first : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₁ main₁ made₁ concl₁))
    (second : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₂ main₂ made₂ concl₂)) :
    (guarded (syntactic _) label).Admits (s := (inferFiring side₁ main₁ made₁ concl₁).firing.result label C)
      (inferFiring side₂ main₂ made₂ concl₂) := by
  have plain := clauseFiring_plain label first
  obtain ⟨present, fresh, made_label, -, inference⟩ :=
    (inferFiring_admits_iff label C side₂ main₂ made₂ concl₂).mp second
  refine (inferFiring_admits_iff label _ side₂ main₂ made₂ concl₂).mpr ⟨fun p member => ⟨?_, (present p member).2⟩,
    ?_, made_label, plain, inference⟩
  · show p.1 ∈ (C.present \ ((([] : List (O × Clause (GroundTerm sig))).map Prod.fst).toFinset)) ∪
      ([(made₁, concl₁)].map Prod.fst).toFinset
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(present p member).1, by simp⟩)
  · show made₂ ∉ (C.present \ ((([] : List (O × Clause (GroundTerm sig))).map Prod.fst).toFinset)) ∪
      ([(made₁, concl₁)].map Prod.fst).toFinset
    simp only [List.map_nil, List.toFinset_nil, Finset.sdiff_empty, List.map_cons, List.toFinset_cons,
      insert_empty_eq, Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨fresh, Ne.symm apart⟩

omit [GroundSimplification sig] in
/-- **Two inferences with different made occurrences are independent.** -/
theorem infer_independent {C : Configuration (Clause (GroundTerm sig)) O}
    {side₁ side₂ : Option (O × Clause (GroundTerm sig))} {main₁ main₂ : O × Clause (GroundTerm sig)}
    {made₁ made₂ : O} {concl₁ concl₂ : Clause (GroundTerm sig)} (apart : made₁ ≠ made₂)
    (first : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₁ main₁ made₁ concl₁))
    (second : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₂ main₂ made₂ concl₂)) :
    (guardedTransport (syntactic _) label).Independent C (inferFiring side₁ main₁ made₁ concl₁)
      (inferFiring side₂ main₂ made₂ concl₂) :=
  (guarded_independent_iff (syntactic _) label).mpr
    ⟨first, second, infer_after label apart first second, infer_after label (Ne.symm apart) second first⟩

omit [GroundSimplification sig] in
/-- **A prover may interleave them**: the two orders are trace-equivalent runs. -/
theorem infer_traceEquiv {C : Configuration (Clause (GroundTerm sig)) O}
    {side₁ side₂ : Option (O × Clause (GroundTerm sig))} {main₁ main₂ : O × Clause (GroundTerm sig)}
    {made₁ made₂ : O} {concl₁ concl₂ : Clause (GroundTerm sig)} (apart : made₁ ≠ made₂)
    (first : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₁ main₁ made₁ concl₁))
    (second : (guarded (syntactic _) label).Admits (s := C) (inferFiring side₂ main₂ made₂ concl₂)) :
    ∃ r r' : (guarded (syntactic _) label).Run C,
      r.word.map Sigma.snd = [inferFiring side₁ main₁ made₁ concl₁, inferFiring side₂ main₂ made₂ concl₂] ∧
      r'.word.map Sigma.snd = [inferFiring side₂ main₂ made₂ concl₂, inferFiring side₁ main₁ made₁ concl₁] ∧
      (guardedTransport (syntactic _) label).TraceEquiv C r r' := by
  obtain ⟨one, two, afterOne, afterTwo, close, swap⟩ := (infer_independent label apart first second).swap
  refine ⟨_, _, rfl, rfl, Relation.EqvGen.rel _ _ (Or.inl (swap (.nil _)))⟩

/-- **A simplification that takes a premise of an inference makes the two dependent**: after it, the
inference is refused. -/
theorem simplify_takes_premise_dependent {C : Configuration (Clause (GroundTerm sig)) O}
    {taken : O × Clause (GroundTerm sig)} {reads makes : List (O × Clause (GroundTerm sig))}
    {side : Option (O × Clause (GroundTerm sig))} {main : O × Clause (GroundTerm sig)} {made : O}
    {concl : Clause (GroundTerm sig)} (premise : taken.1 ∈ (side.toList ++ [main]).map Prod.fst)
    (simplified : (guarded (syntactic _) label).Admits (s := C) (simplifyFiring taken reads makes)) :
    ¬ (guarded (syntactic _) label).Admits (s := (simplifyFiring taken reads makes).firing.result label C)
        (inferFiring side main made concl) ∧
      ¬ (guardedTransport (syntactic _) label).Independent C (simplifyFiring taken reads makes)
        (inferFiring side main made concl) := by
  have refused : ¬ (guarded (syntactic _) label).Admits
      (s := (simplifyFiring taken reads makes).firing.result label C) (inferFiring side main made concl) := by
    intro admitted
    obtain ⟨present, -⟩ := (inferFiring_admits_iff label _ side main made concl).mp admitted
    obtain ⟨p, member, same⟩ := List.mem_map.mp premise
    have gone := (simplify_takes_redundant label simplified).1
    rw [← same] at gone
    exact gone (present p member).1
  exact ⟨refused, fun independent =>
    refused ((guarded_independent_iff (syntactic _) label).mp independent).2.2.1⟩

end Inferences

#print axioms syntactic_models_iff
#print axioms pairs_eq
#print axioms clauseFiring_models_iff
#print axioms clauseFiring_admits_iff
#print axioms clauseFiring_plain
#print axioms inferFiring_admits_iff
#print axioms infer_clauses
#print axioms Simplification.redundant
#print axioms simplify_takes_redundant
#print axioms infer_after
#print axioms infer_independent
#print axioms infer_traceEquiv
#print axioms simplify_takes_premise_dependent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
