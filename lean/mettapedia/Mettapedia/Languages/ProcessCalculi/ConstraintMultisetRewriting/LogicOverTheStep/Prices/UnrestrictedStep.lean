import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

/-!
# Hennessy–Milner adequacy on the unrestricted first-order step

`ProgramAdequacy.program_adequacy` proves finitary adequacy (logical equivalence is bisimilarity) on
the first-order step under every finite program, for every observation set invariant under renaming.
`ProgramAdequacy.base_not_imageFiniteBisimilar` shows that the finite-cover route is unavailable on
the unrestricted step, where every rule instance is admitted. This module settles what holds there.

## One firing reaches every extension of the knowledge

On ground terms a consistent store holds only equations between a term and itself
(`ground_consistent_iff`). Every firing extends the knowledge by such equations (`succ_extends`), and
every such extension is one firing away, by a rule that only tells (`succ_tell`). On knowledge, the
unrestricted step is therefore the reflexive and transitive prefix order of lists of equations.

## Adequacy for the observation sets of the tree

* **Observing the knowledge** (`knowledgeView`): having the same knowledge is a bisimulation
  (`sameKnowledge_isBisimulation`), so logical equivalence, bisimilarity and equal knowledge coincide
  (`knowledgeView_adequacy`).
* **Observing the knowledge and the bag of labels** (`storeView`): stores with the same knowledge and
  the same bag are renamings of each other (`renamed_of_sameView`), renaming is a bisimulation of the
  unrestricted step (`renamed_isBisimulation_base`), so adequacy holds (`storeView_adequacy_base`),
  although no finite cover exists (`ProgramAdequacy.base_not_imageFiniteBisimilar`).

Both are decided at depth zero: the atoms already separate what bisimilarity separates.

## Adequacy fails for a coarser observation set

`tagView` reads only the knowledge: for each `n`, whether it is `[a = a, n = n]` or `[b = b, n = n]`
(the tag `n`), and whether it is tagged or `[b = b, w = w]` (the mark). It is invariant under
renaming, so `program_adequacy` applies to it under every finite program (`tagView_program_adequacy`).
On the unrestricted step the stores with knowledge `[a = a]` and `[b = b]` are logically equivalent
(`roots_logicallyEquivalent`) and not bisimilar (`roots_not_bisimilar`): the second reaches the
marked store `[b = b, w = w]`, which carries no tag, and the first reaches only tagged marked stores.
Every formula mentions finitely many tags, and a tag it does not mention imitates the untagged
store (`wit_sat_iff_tag`).

So without a finite program, adequacy holds or fails according to the observation set: the form of
`program_adequacy` quantified over all observation sets invariant under renaming is false on the
unrestricted step (`unrestricted_adequacy_fails`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.UnrestrictedStep

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open StepSpan ProgramAdequacy
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-! ## Ground stores and the successors of the unrestricted step -/

/-- Every equation of the store is between a term and itself. -/
def SelfEquated (store : EquationStore Expr) : Prop := ∀ e ∈ store, e.1 = e.2

/-- **On ground terms a store is consistent exactly when every equation is `e = e`.** -/
theorem ground_consistent_iff (store : EquationStore Expr) :
    ground.Consistent store ↔ SelfEquated store :=
  ⟨fun ⟨_, solved⟩ => solved, fun selfEquated => ⟨(), selfEquated⟩⟩

theorem selfEquated_append {first second : EquationStore Expr} :
    SelfEquated (first ++ second) ↔ SelfEquated first ∧ SelfEquated second := by
  constructor
  · intro all
    exact ⟨fun e member => all e (List.mem_append_left _ member),
      fun e member => all e (List.mem_append_right _ member)⟩
  · rintro ⟨one, two⟩ e member
    rcases List.mem_append.mp member with member | member
    · exact one e member
    · exact two e member

/-- The successors of the unrestricted step: a rule instance, a valid selection, its result.
Predicate queries add no successor. -/
theorem base_succ_iff (C C' : Conf) :
    Succ base C C' ↔ ∃ (rule : RuleInstance Expr) (sel : Selection Occ),
      sel.Valid ground Prod.fst rule C ∧ sel.result Prod.fst rule C = C' := by
  constructor
  · rintro ⟨f, valid, reached⟩
    exact ⟨f.rule, f.selection, (show f.Valid ground Prod.fst C from valid).firing, reached⟩
  · rintro ⟨rule, sel, valid, reached⟩
    exact ⟨⟨rule, [], sel⟩, PredicateQueryAdmission.regionValid_nil_iff.mpr valid, reached⟩

/-- **Every firing extends the knowledge**, by equations between a term and itself; the result is
consistent. -/
theorem succ_extends {C C' : Conf} (step : Succ base C C') :
    ∃ L : EquationStore Expr, C'.equations = C.equations ++ L ∧ SelfEquated C'.equations := by
  obtain ⟨rule, sel, valid, rfl⟩ := (base_succ_iff C C').mp step
  refine ⟨Selection.equations Prod.fst rule.take sel.taken ++
      Selection.equations Prod.fst rule.read sel.read ++ rule.tell, ?_, ?_⟩
  · simp only [Selection.result, Selection.problem, List.append_assoc]
  · exact (ground_consistent_iff _).mp valid.consistent

/-- The rule that only tells `L`. -/
def tells (L : EquationStore Expr) : RuleInstance Expr := ⟨[], [], L, [], []⟩

/-- The selection that takes, reads and makes nothing. -/
def noSelection : Selection Occ := ⟨[], [], []⟩

theorem tells_valid {C : Conf} {L : EquationStore Expr} (selfEquated : SelfEquated (C.equations ++ L)) :
    noSelection.Valid ground Prod.fst (tells L) C where
  take_distinct := List.nodup_nil
  output_distinct := List.nodup_nil
  take_length := rfl
  read_length := rfl
  outputs := rfl
  occurrences := ⟨by simp [noSelection, Selection.commit], by simp [noSelection, Selection.commit],
    by simp [noSelection, Selection.commit], by simp [noSelection, Selection.commit],
    fun _ member => by simp [Selection.commit] at member⟩
  consistent := (ground_consistent_iff _).mpr (by
    simpa [Selection.problem, Selection.equations, noSelection, tells] using selfEquated)
  checks := fun _ member => by simp [tells] at member

theorem tells_result (C : Conf) (L : EquationStore Expr) :
    noSelection.result Prod.fst (tells L) C = ⟨C.equations ++ L, C.present⟩ := by
  simp [Selection.result, Selection.problem, Selection.equations, noSelection, tells, fire,
    Selection.commit]

/-- **Every consistent extension of the knowledge is one firing away**: the rule that only tells it. -/
theorem succ_tell {C : Conf} {L : EquationStore Expr} (selfEquated : SelfEquated (C.equations ++ L)) :
    Succ base C ⟨C.equations ++ L, C.present⟩ :=
  (base_succ_iff _ _).mpr ⟨tells L, noSelection, tells_valid selfEquated, tells_result C L⟩

/-- A consistent store steps to itself. -/
theorem succ_self {C : Conf} (selfEquated : SelfEquated C.equations) : Succ base C C := by
  have step := succ_tell (C := C) (L := []) (by rwa [List.append_nil])
  rw [List.append_nil] at step
  exact step

/-! ## Adequacy when the knowledge is observed -/

/-- **Observing the knowledge**: one atom per store of equations. -/
def knowledgeView : EquationStore Expr → Conf → Prop := fun knowledge C => C.equations = knowledge

/-- **Having the same knowledge is a bisimulation of the unrestricted step**, for every observation set
that reads only the knowledge. -/
theorem sameKnowledge_isBisimulation {Atom : Type} (observes : Atom → Conf → Prop)
    (reads : ∀ (a : Atom) {C D : Conf}, C.equations = D.equations → (observes a C ↔ observes a D)) :
    (stepSystem base observes).IsBisimulation (fun C D : Conf => C.equations = D.equations) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C D same _ C' step
    obtain ⟨L, extended, selfEquated⟩ := succ_extends step
    refine ⟨⟨D.equations ++ L, D.present⟩, succ_tell ?_, ?_⟩
    · rw [← same, ← extended]
      exact selfEquated
    · show C'.equations = D.equations ++ L
      rw [extended, same]
  · intro C D same _ D' step
    obtain ⟨L, extended, selfEquated⟩ := succ_extends step
    refine ⟨⟨C.equations ++ L, C.present⟩, succ_tell ?_, ?_⟩
    · rw [same, ← extended]
      exact selfEquated
    · show C.equations ++ L = D'.equations
      rw [extended, same]
  · intro C D same a
    exact reads a same

/-- **Observing the knowledge, adequacy holds on the unrestricted step**, and bisimilarity is equal
knowledge. -/
theorem knowledgeView_adequacy (C D : Conf) :
    ((stepSystem base knowledgeView).LogicallyEquivalent C D ↔
        (stepSystem base knowledgeView).Bisimilar C D) ∧
      ((stepSystem base knowledgeView).Bisimilar C D ↔ C.equations = D.equations) := by
  have bisimulation := sameKnowledge_isBisimulation knowledgeView
    (fun a C D same => by simp only [knowledgeView, same])
  have same_of_equivalent : (stepSystem base knowledgeView).LogicallyEquivalent C D →
      C.equations = D.equations := by
    intro equivalent
    have atD : D.equations = C.equations := (equivalent (.atom C.equations)).mp rfl
    exact atD.symm
  refine ⟨⟨fun equivalent => ⟨_, bisimulation, same_of_equivalent equivalent⟩,
    (stepSystem base knowledgeView).logicallyEquivalent_of_bisimilar⟩, ?_⟩
  exact ⟨fun bisimilar => same_of_equivalent
      ((stepSystem base knowledgeView).logicallyEquivalent_of_bisimilar bisimilar),
    fun same => ⟨_, bisimulation, same⟩⟩

/-! ## Adequacy when the knowledge and the bag of labels are observed -/

/-- **Renaming is a bisimulation of the unrestricted step**, for observations that cannot see
identities. -/
theorem renamed_isBisimulation_base {Atom : Type} (observes : Atom → Conf → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm Occ) (C : Conf), Keeps Prod.fst π →
      (observes a (renameConf π C) ↔ observes a C)) :
    (stepSystem base observes).IsBisimulation (Renamed Prod.fst) := by
  have succ_renamed : ∀ {C D C' : Conf}, Renamed Prod.fst C D → Succ base C C' →
      ∃ D', Succ base D D' ∧ Renamed Prod.fst C' D' := by
    rintro C D C' ⟨π, keeps, rfl⟩ step
    obtain ⟨rule, sel, valid, rfl⟩ := (base_succ_iff C C').mp step
    exact ⟨renameConf π (sel.result Prod.fst rule C), (base_succ_iff _ _).mpr
      ⟨rule, renameSel π sel, valid_rename ground Prod.fst keeps valid,
        result_rename Prod.fst keeps sel rule C⟩, π, keeps, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro C D renamed _ C' step
    exact succ_renamed renamed step
  · intro C D renamed _ D' step
    obtain ⟨C', back, renamed'⟩ := succ_renamed (renamed_symm Prod.fst renamed) step
    exact ⟨C', back, renamed_symm Prod.fst renamed'⟩
  · rintro C D ⟨π, keeps, rfl⟩ a
    exact (invariant a π C keeps).symm

/-- A listing of a finite set of occurrences with prescribed labels, when the bags of labels agree. -/
theorem exists_listing : ∀ (m : List Occ) (P : Finset Occ),
    ((m.map Prod.fst : List Expr) : Multiset Expr) = P.val.map Prod.fst →
      ∃ m' : List Occ, m'.Nodup ∧ m'.toFinset = P ∧ m'.map Prod.fst = m.map Prod.fst
  | [], P, bags => by
      have mapped : P.val.map Prod.fst = 0 := by simpa using bags.symm
      have empty : P = ∅ := Finset.val_eq_zero.mp (Multiset.map_eq_zero.mp mapped)
      exact ⟨[], List.nodup_nil, by simp [empty], rfl⟩
  | o :: rest, P, bags => by
      have member : o.1 ∈ P.val.map Prod.fst := by
        rw [← bags]
        simp
      obtain ⟨o', inside, labelled⟩ := Multiset.mem_map.mp member
      have bags' : ((rest.map Prod.fst : List Expr) : Multiset Expr) =
          (P.erase o').val.map Prod.fst := by
        rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ inside, ← bags, labelled]
        simp
      obtain ⟨m', nodup, cover, labels⟩ := exists_listing rest (P.erase o') bags'
      refine ⟨o' :: m', List.nodup_cons.mpr ⟨fun inM => ?_, nodup⟩, ?_, ?_⟩
      · have erased : o' ∈ P.erase o' := cover ▸ List.mem_toFinset.mpr inM
        exact Finset.notMem_erase o' P erased
      · rw [List.toFinset_cons, cover, Finset.insert_erase inside]
      · simp [labels, labelled]

/-- **Stores with the same knowledge and the same bag of labels are renamings of each other.** -/
theorem renamed_of_sameView {C D : Conf} (knowledge : C.equations = D.equations)
    (bags : C.present.val.map Prod.fst = D.present.val.map Prod.fst) : Renamed Prod.fst C D := by
  obtain ⟨m', nodup', cover', labels'⟩ := exists_listing C.present.toList D.present (by
    rw [← bags, ← Finset.coe_toList C.present]
    rfl)
  obtain ⟨π, keeps, -, mapped⟩ := exists_renaming Prod.fst C.present.toList m'
    (Finset.nodup_toList _) nodup' labels'.symm ∅ (by simp) (by simp)
  refine ⟨π, keeps, ?_⟩
  have present : D.present = C.present.map π.toEmbedding := by
    rw [← cover', ← mapped, ProgramAdequacy.toFinset_map, Finset.toList_toFinset]
  show D = ⟨C.equations, C.present.map π.toEmbedding⟩
  rw [← present, knowledge]

/-- **Observing the knowledge and the bag of labels, adequacy holds on the unrestricted step**, with
no finite program and no finite cover. -/
theorem storeView_adequacy_base (C D : Conf) :
    (stepSystem base storeView).LogicallyEquivalent C D ↔ (stepSystem base storeView).Bisimilar C D := by
  refine ⟨fun equivalent => ?_, (stepSystem base storeView).logicallyEquivalent_of_bisimilar⟩
  have bagAtD : D.present.val.map Prod.fst = C.present.val.map Prod.fst :=
    (equivalent (.atom (.inl (C.present.val.map Prod.fst)))).mp rfl
  have knowledgeAtD : D.equations = C.equations := (equivalent (.atom (.inr C.equations))).mp rfl
  exact ⟨Renamed Prod.fst, renamed_isBisimulation_base storeView storeView_invariant,
    renamed_of_sameView knowledgeAtD.symm bagAtD.symm⟩

/-! ## A coarser observation set, and where adequacy fails -/

/-- The equation of a term with itself. -/
def selfEq (e : Expr) : Expr × Expr := (e, e)

/-- The first root. -/
def rootA : Expr := .sym 0
/-- The second root. -/
def rootB : Expr := .sym 1
/-- The untagged witness. -/
def wit : Expr := .sym 2

/-- The knowledge of the untagged marked store. -/
def witKnowledge : EquationStore Expr := [selfEq rootB, selfEq wit]

/-- The knowledge `[x = x, n = n]`, for `x` one of the two roots. -/
def Tagged (n : ℕ) (E : EquationStore Expr) : Prop :=
  E = [selfEq rootA, selfEq (.name n)] ∨ E = [selfEq rootB, selfEq (.name n)]

/-- The marked knowledge: the untagged witness or a tagged store. -/
def Marked (E : EquationStore Expr) : Prop := E = witKnowledge ∨ ∃ n, Tagged n E

/-- **The coarser observation set**: `some n` reads the tag `n`, `none` reads the mark. -/
def tagView : Option ℕ → Conf → Prop
  | some n, C => Tagged n C.equations
  | none, C => Marked C.equations

/-- `tagView` reads only the knowledge, so renaming identities does not change it. -/
theorem tagView_invariant (a : Option ℕ) (π : Equiv.Perm Occ) (C : Conf) (_ : Keeps Prod.fst π) :
    tagView a (renameConf π C) ↔ tagView a C := by
  cases a <;> exact Iff.rfl

/-- **Under every finite program the coarser observation set is adequate** (`program_adequacy`). -/
theorem tagView_program_adequacy {R : Set (RuleInstance Expr)} (finite : R.Finite) (C D : Conf) :
    (stepSystem (program ground Prod.fst R) tagView).LogicallyEquivalent C D ↔
      (stepSystem (program ground Prod.fst R) tagView).Bisimilar C D :=
  program_adequacy ground Prod.fst occSupply finite tagView tagView_invariant C D

/-- The knowledge the observation set tells apart; every other store is junk. -/
def Shaped (E : EquationStore Expr) : Prop :=
  E = [] ∨ E = [selfEq rootA] ∨ E = [selfEq rootB] ∨ Marked E

/-- A consistent store whose knowledge is not shaped. -/
def Junk (C : Conf) : Prop := SelfEquated C.equations ∧ ¬ Shaped C.equations

theorem selfEquated_single (x : Expr) : SelfEquated [selfEq x] := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

theorem selfEquated_pair (x y : Expr) : SelfEquated [selfEq x, selfEq y] := by
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · rw [List.mem_singleton.mp member]
    rfl

theorem tagged_selfEquated {n : ℕ} {E : EquationStore Expr} (tagged : Tagged n E) : SelfEquated E := by
  rcases tagged with rfl | rfl <;> exact selfEquated_pair _ _

theorem tagged_length {n : ℕ} {E : EquationStore Expr} (tagged : Tagged n E) : E.length = 2 := by
  rcases tagged with rfl | rfl <;> rfl

/-- A tagged store carries exactly one tag. -/
theorem tagged_iff {k n : ℕ} {E : EquationStore Expr} (tagged : Tagged n E) : Tagged k E ↔ k = n := by
  constructor
  · intro other
    rcases tagged with rfl | rfl <;> rcases other with h | h <;>
      simp [selfEq, rootA, rootB] at h <;> omega
  · rintro rfl
    exact tagged

theorem not_tagged_wit (k : ℕ) : ¬ Tagged k witKnowledge := by
  rintro (h | h) <;> simp [witKnowledge, selfEq, rootA, rootB, wit] at h

theorem not_marked_single (x : Expr × Expr) : ¬ Marked [x] := by
  rintro (h | ⟨n, h | h⟩) <;> simp [witKnowledge] at h

theorem shaped_length {E : EquationStore Expr} (shaped : Shaped E) : E.length ≤ 2 := by
  rcases shaped with rfl | rfl | rfl | rfl | ⟨n, rfl | rfl⟩ <;> simp [witKnowledge]

theorem prefix_of_append_eq_single {E L : EquationStore Expr} {a : Expr × Expr} (h : E ++ L = [a]) :
    E = [] ∨ E = [a] := by
  rcases E with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact Or.inl rfl
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inr (by rw [h.1])
  · simp at h

theorem prefix_of_append_eq_pair {E L : EquationStore Expr} {a b : Expr × Expr} (h : E ++ L = [a, b]) :
    E = [] ∨ E = [a] ∨ E = [a, b] := by
  rcases E with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · exact Or.inl rfl
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inr (Or.inl (by rw [h.1]))
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inr (Or.inr (by rw [h.1, h.2.1]))
  · simp at h

/-- **Shaped knowledge is closed under prefixes**, so junk is closed under extension. -/
theorem shaped_of_append {E L : EquationStore Expr} (shaped : Shaped (E ++ L)) : Shaped E := by
  rcases shaped with h | h | h | h | ⟨n, h | h⟩
  · exact Or.inl (List.append_eq_nil_iff.mp h).1
  · rcases prefix_of_append_eq_single h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases prefix_of_append_eq_single h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rcases prefix_of_append_eq_pair h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rcases prefix_of_append_eq_pair h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inl rfl⟩)))
  · rcases prefix_of_append_eq_pair h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr rfl⟩)))

/-- The extensions of the first root: itself, a tag, or junk. -/
theorem rootA_extension (L : EquationStore Expr) :
    L = [] ∨ (∃ n, L = [selfEq (.name n)]) ∨ ¬ Shaped ([selfEq rootA] ++ L) := by
  by_cases shaped : Shaped ([selfEq rootA] ++ L)
  · rcases shaped with h | h | h | h | ⟨n, h | h⟩
    · simp at h
    · exact Or.inl (by simpa using h)
    · simp [selfEq, rootA, rootB] at h
    · simp [witKnowledge, selfEq, rootA, rootB] at h
    · exact Or.inr (Or.inl ⟨n, by simpa using h⟩)
    · simp [selfEq, rootA, rootB] at h
  · exact Or.inr (Or.inr shaped)

/-- The extensions of the second root: itself, the untagged witness, a tag, or junk. -/
theorem rootB_extension (L : EquationStore Expr) :
    L = [] ∨ L = [selfEq wit] ∨ (∃ n, L = [selfEq (.name n)]) ∨ ¬ Shaped ([selfEq rootB] ++ L) := by
  by_cases shaped : Shaped ([selfEq rootB] ++ L)
  · rcases shaped with h | h | h | h | ⟨n, h | h⟩
    · simp at h
    · simp [selfEq, rootA, rootB] at h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl (by simpa [witKnowledge] using h))
    · simp [selfEq, rootA, rootB] at h
    · exact Or.inr (Or.inr (Or.inl ⟨n, by simpa using h⟩))
  · exact Or.inr (Or.inr (Or.inr shaped))

/-- A store of two equations extends only to itself or to junk. -/
theorem pair_extension {E L : EquationStore Expr} (two : E.length = 2) :
    L = [] ∨ ¬ Shaped (E ++ L) := by
  by_cases shaped : Shaped (E ++ L)
  · left
    have bound := shaped_length shaped
    rw [List.length_append, two] at bound
    exact List.length_eq_zero_iff.mp (by omega)
  · exact Or.inr shaped

/-- An extension whose knowledge is not shaped is junk. -/
theorem junk_of_extension {C' : Conf} {E L : EquationStore Expr} (extended : C'.equations = E ++ L)
    (selfEquated : SelfEquated C'.equations) (unshaped : ¬ Shaped (E ++ L)) : Junk C' :=
  ⟨selfEquated, fun shaped => unshaped (extended ▸ shaped)⟩

/-- Three more equations make any consistent store junk. -/
def toJunk (C : Conf) : Conf := ⟨C.equations ++ [selfEq rootA, selfEq rootA, selfEq rootA], C.present⟩

theorem selfEquated_tail : SelfEquated [selfEq rootA, selfEq rootA, selfEq rootA] := by
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  rw [member]
  rfl

theorem succ_toJunk {C : Conf} (selfEquated : SelfEquated C.equations) : Succ base C (toJunk C) :=
  succ_tell (selfEquated_append.mpr ⟨selfEquated, selfEquated_tail⟩)

theorem junk_toJunk {C : Conf} (selfEquated : SelfEquated C.equations) : Junk (toJunk C) := by
  refine ⟨selfEquated_append.mpr ⟨selfEquated, selfEquated_tail⟩, fun shaped => ?_⟩
  have bound := shaped_length shaped
  simp only [toJunk, List.length_append, List.length_cons, List.length_nil] at bound
  omega

theorem junk_unobserved {C : Conf} (junk : Junk C) (a : Option ℕ) : ¬ tagView a C := by
  cases a with
  | none => exact fun marked => junk.2 (Or.inr (Or.inr (Or.inr marked)))
  | some n => exact fun tagged => junk.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, tagged⟩))))

/-- **All junk is bisimilar**: it is unobserved and steps only to junk. -/
theorem junk_isBisimulation :
    (stepSystem base tagView).IsBisimulation (fun C D : Conf => Junk C ∧ Junk D) := by
  have forth : ∀ {C D C' : Conf}, Junk C → Junk D → Succ base C C' → Succ base D D ∧ Junk C' := by
    intro C D C' junkC junkD step
    obtain ⟨L, extended, selfEquated⟩ := succ_extends step
    refine ⟨succ_self junkD.1, selfEquated, fun shaped => junkC.2 (shaped_of_append (L := L) ?_)⟩
    rw [← extended]
    exact shaped
  refine ⟨?_, ?_, ?_⟩
  · rintro C D ⟨junkC, junkD⟩ _ C' step
    obtain ⟨self, junkC'⟩ := forth junkC junkD step
    exact ⟨D, self, junkC', junkD⟩
  · rintro C D ⟨junkC, junkD⟩ _ D' step
    obtain ⟨self, junkD'⟩ := forth junkD junkC step
    exact ⟨C, self, junkC, junkD'⟩
  · rintro C D ⟨junkC, junkD⟩ a
    exact iff_of_false (junk_unobserved junkC a) (junk_unobserved junkD a)

theorem junk_sat_iff {C D : Conf} (junkC : Junk C) (junkD : Junk D) (φ : Formula (Option ℕ) Unit) :
    (stepSystem base tagView).sat φ C ↔ (stepSystem base tagView).sat φ D :=
  (stepSystem base tagView).sat_iff_of_isBisimulation junk_isBisimulation φ ⟨junkC, junkD⟩

/-- Stores with the same tag satisfy the same formulas. -/
theorem tagged_sat_iff (φ : Formula (Option ℕ) Unit) : ∀ (n : ℕ) (C D : Conf),
    Tagged n C.equations → Tagged n D.equations →
      ((stepSystem base tagView).sat φ C ↔ (stepSystem base tagView).sat φ D) := by
  induction φ with
  | top => intros; exact Iff.rfl
  | atom a =>
    intro n C D taggedC taggedD
    cases a with
    | none => exact iff_of_true (Or.inr ⟨n, taggedC⟩) (Or.inr ⟨n, taggedD⟩)
    | some k => exact (tagged_iff taggedC).trans (tagged_iff taggedD).symm
  | conj φ ψ ihφ ihψ =>
    intro n C D taggedC taggedD
    exact and_congr (ihφ n C D taggedC taggedD) (ihψ n C D taggedC taggedD)
  | neg φ ih =>
    intro n C D taggedC taggedD
    exact not_congr (ih n C D taggedC taggedD)
  | dia l φ ih =>
    intro n C D taggedC taggedD
    have side : ∀ {X Y : Conf}, Tagged n X.equations → Tagged n Y.equations →
        (stepSystem base tagView).sat (.dia l φ) X → (stepSystem base tagView).sat (.dia l φ) Y := by
      rintro X Y taggedX taggedY ⟨X', step, holds⟩
      obtain ⟨L, extended, selfEquated⟩ := succ_extends step
      rcases pair_extension (L := L) (tagged_length taggedX) with rfl | unshaped
      · have taggedX' : Tagged n X'.equations := by
          rw [extended, List.append_nil]
          exact taggedX
        exact ⟨Y, succ_self (tagged_selfEquated taggedY), (ih n X' Y taggedX' taggedY).mp holds⟩
      · exact ⟨toJunk Y, succ_toJunk (tagged_selfEquated taggedY),
          (junk_sat_iff (junk_of_extension extended selfEquated unshaped)
            (junk_toJunk (tagged_selfEquated taggedY)) φ).mp holds⟩
    exact ⟨side taggedC taggedD, side taggedD taggedC⟩

/-- **A tag the formula does not mention imitates the untagged witness.** -/
theorem wit_sat_iff_tag (φ : Formula (Option ℕ) Unit) : ∃ bound : ℕ, ∀ n, bound ≤ n →
    ∀ C D : Conf, C.equations = witKnowledge → Tagged n D.equations →
      ((stepSystem base tagView).sat φ C ↔ (stepSystem base tagView).sat φ D) := by
  induction φ with
  | top => exact ⟨0, fun _ _ _ _ _ _ => Iff.rfl⟩
  | atom a =>
    cases a with
    | none =>
      refine ⟨0, fun n _ C D witC taggedD => iff_of_true ?_ (Or.inr ⟨n, taggedD⟩)⟩
      show Marked C.equations
      rw [witC]
      exact Or.inl rfl
    | some k =>
      refine ⟨k + 1, fun n bound C D witC taggedD => iff_of_false ?_ ?_⟩
      · show ¬ Tagged k C.equations
        rw [witC]
        exact not_tagged_wit k
      · show ¬ Tagged k D.equations
        intro taggedK
        have same := (tagged_iff taggedD).mp taggedK
        omega
  | conj φ ψ ihφ ihψ =>
    obtain ⟨first, hφ⟩ := ihφ
    obtain ⟨second, hψ⟩ := ihψ
    exact ⟨max first second, fun n bound C D witC taggedD =>
      and_congr (hφ n (le_of_max_le_left bound) C D witC taggedD)
        (hψ n (le_of_max_le_right bound) C D witC taggedD)⟩
  | neg φ ih =>
    obtain ⟨b, h⟩ := ih
    exact ⟨b, fun n bound C D witC taggedD => not_congr (h n bound C D witC taggedD)⟩
  | dia l φ ih =>
    obtain ⟨b, h⟩ := ih
    refine ⟨b, fun n bound C D witC taggedD => ⟨?_, ?_⟩⟩
    · rintro ⟨C', step, holds⟩
      obtain ⟨L, extended, selfEquated⟩ := succ_extends step
      have selfD := tagged_selfEquated taggedD
      have two : C.equations.length = 2 := by rw [witC]; rfl
      rcases pair_extension (L := L) two with rfl | unshaped
      · have witC' : C'.equations = witKnowledge := by rw [extended, List.append_nil, witC]
        exact ⟨D, succ_self selfD, (h n bound C' D witC' taggedD).mp holds⟩
      · exact ⟨toJunk D, succ_toJunk selfD,
          (junk_sat_iff (junk_of_extension extended selfEquated unshaped) (junk_toJunk selfD) φ).mp holds⟩
    · rintro ⟨D', step, holds⟩
      obtain ⟨L, extended, selfEquated⟩ := succ_extends step
      have selfC : SelfEquated C.equations := by rw [witC]; exact selfEquated_pair _ _
      rcases pair_extension (L := L) (tagged_length taggedD) with rfl | unshaped
      · have taggedD' : Tagged n D'.equations := by
          rw [extended, List.append_nil]
          exact taggedD
        exact ⟨C, succ_self selfC, (h n bound C D' witC taggedD').mpr holds⟩
      · exact ⟨toJunk C, succ_toJunk selfC,
          (junk_sat_iff (junk_of_extension extended selfEquated unshaped) (junk_toJunk selfC) φ).mp holds⟩

/-- **The two roots satisfy the same formulas.** -/
theorem roots_sat_iff (φ : Formula (Option ℕ) Unit) : ∀ C D : Conf,
    C.equations = [selfEq rootA] → D.equations = [selfEq rootB] →
      ((stepSystem base tagView).sat φ C ↔ (stepSystem base tagView).sat φ D) := by
  induction φ with
  | top => intros; exact Iff.rfl
  | atom a =>
    intro C D rootC rootD
    cases a with
    | none =>
      refine iff_of_false ?_ ?_
      · show ¬ Marked C.equations
        rw [rootC]
        exact not_marked_single _
      · show ¬ Marked D.equations
        rw [rootD]
        exact not_marked_single _
    | some k =>
      refine iff_of_false ?_ ?_
      · show ¬ Tagged k C.equations
        rw [rootC]
        exact fun tagged => not_marked_single _ (Or.inr ⟨k, tagged⟩)
      · show ¬ Tagged k D.equations
        rw [rootD]
        exact fun tagged => not_marked_single _ (Or.inr ⟨k, tagged⟩)
  | conj φ ψ ihφ ihψ =>
    intro C D rootC rootD
    exact and_congr (ihφ C D rootC rootD) (ihψ C D rootC rootD)
  | neg φ ih =>
    intro C D rootC rootD
    exact not_congr (ih C D rootC rootD)
  | dia l φ ih =>
    intro C D rootC rootD
    have selfC : SelfEquated C.equations := by rw [rootC]; exact selfEquated_single _
    have selfD : SelfEquated D.equations := by rw [rootD]; exact selfEquated_single _
    constructor
    · rintro ⟨C', step, holds⟩
      obtain ⟨L, extended, selfEquated⟩ := succ_extends step
      rw [rootC] at extended
      rcases rootA_extension L with rfl | ⟨n, rfl⟩ | unshaped
      · have rootC' : C'.equations = [selfEq rootA] := by rw [extended, List.append_nil]
        exact ⟨D, succ_self selfD, (ih C' D rootC' rootD).mp holds⟩
      · have taggedC' : Tagged n C'.equations := by rw [extended]; exact Or.inl rfl
        have selfTag : SelfEquated (D.equations ++ [selfEq (.name n)]) := by
          rw [rootD]; exact selfEquated_pair _ _
        have taggedD' : Tagged n (D.equations ++ [selfEq (.name n)]) := by
          rw [rootD]; exact Or.inr rfl
        exact ⟨⟨D.equations ++ [selfEq (.name n)], D.present⟩, succ_tell selfTag,
          (tagged_sat_iff φ n C' ⟨D.equations ++ [selfEq (.name n)], D.present⟩ taggedC'
            taggedD').mp holds⟩
      · exact ⟨toJunk D, succ_toJunk selfD,
          (junk_sat_iff (junk_of_extension extended selfEquated unshaped) (junk_toJunk selfD) φ).mp holds⟩
    · rintro ⟨D', step, holds⟩
      obtain ⟨L, extended, selfEquated⟩ := succ_extends step
      rw [rootD] at extended
      rcases rootB_extension L with rfl | rfl | ⟨n, rfl⟩ | unshaped
      · have rootD' : D'.equations = [selfEq rootB] := by rw [extended, List.append_nil]
        exact ⟨C, succ_self selfC, (ih C D' rootC rootD').mpr holds⟩
      · obtain ⟨b, h⟩ := wit_sat_iff_tag φ
        have witD' : D'.equations = witKnowledge := by rw [extended]; rfl
        have selfTag : SelfEquated (C.equations ++ [selfEq (.name b)]) := by
          rw [rootC]; exact selfEquated_pair _ _
        have taggedC' : Tagged b (C.equations ++ [selfEq (.name b)]) := by
          rw [rootC]; exact Or.inl rfl
        exact ⟨⟨C.equations ++ [selfEq (.name b)], C.present⟩, succ_tell selfTag,
          (h b le_rfl D' ⟨C.equations ++ [selfEq (.name b)], C.present⟩ witD' taggedC').mp holds⟩
      · have taggedD' : Tagged n D'.equations := by rw [extended]; exact Or.inr rfl
        have selfTag : SelfEquated (C.equations ++ [selfEq (.name n)]) := by
          rw [rootC]; exact selfEquated_pair _ _
        have taggedC' : Tagged n (C.equations ++ [selfEq (.name n)]) := by
          rw [rootC]; exact Or.inl rfl
        exact ⟨⟨C.equations ++ [selfEq (.name n)], C.present⟩, succ_tell selfTag,
          (tagged_sat_iff φ n D' ⟨C.equations ++ [selfEq (.name n)], C.present⟩ taggedD'
            taggedC').mp holds⟩
      · exact ⟨toJunk C, succ_toJunk selfC,
          (junk_sat_iff (junk_of_extension extended selfEquated unshaped) (junk_toJunk selfC) φ).mp holds⟩

/-- The store of the first root. -/
def rootAConf : Conf := ⟨[selfEq rootA], ∅⟩
/-- The store of the second root. -/
def rootBConf : Conf := ⟨[selfEq rootB], ∅⟩
/-- The untagged marked store. -/
def witConf : Conf := ⟨witKnowledge, ∅⟩

/-- **The two roots are logically equivalent on the unrestricted step.** -/
theorem roots_logicallyEquivalent :
    (stepSystem base tagView).LogicallyEquivalent rootAConf rootBConf :=
  fun φ => roots_sat_iff φ rootAConf rootBConf rfl rfl

/-- The second root reaches the untagged marked store in one firing. -/
theorem rootB_reaches_wit : Succ base rootBConf witConf :=
  succ_tell (C := rootBConf) (L := [selfEq wit]) (selfEquated_pair _ _)

/-- **The two roots are not bisimilar on the unrestricted step**: the untagged marked store has no
match among the successors of the first root. -/
theorem roots_not_bisimilar : ¬ (stepSystem base tagView).Bisimilar rootAConf rootBConf := by
  rintro ⟨R, bisimulation, related⟩
  obtain ⟨C', step, relatedWit⟩ := bisimulation.2.1 related () rootB_reaches_wit
  have agree := fun φ : Formula (Option ℕ) Unit =>
    (stepSystem base tagView).sat_iff_of_isBisimulation bisimulation φ relatedWit
  have markedC' : Marked C'.equations := (agree (.atom none)).mpr (Or.inl rfl)
  obtain ⟨L, extended, -⟩ := succ_extends step
  have tagged : ∃ n, Tagged n C'.equations := by
    rcases markedC' with h | ⟨n, h⟩
    · rw [extended] at h
      simp [rootAConf, witKnowledge, selfEq, rootA, rootB] at h
    · exact ⟨n, h⟩
  obtain ⟨n, taggedC'⟩ := tagged
  exact not_tagged_wit n ((agree (.atom (some n))).mp taggedC')

/-- **Without a finite program, finitary adequacy fails for some observation set invariant under
renaming**, while it holds for the same observation set under every finite program
(`tagView_program_adequacy`) and on the unrestricted step for `knowledgeView` and `storeView`. -/
theorem unrestricted_adequacy_fails :
    ∃ (Atom : Type) (observes : Atom → Conf → Prop),
      (∀ (a : Atom) (π : Equiv.Perm Occ) (C : Conf), Keeps Prod.fst π →
        (observes a (renameConf π C) ↔ observes a C)) ∧
      ∃ C D : Conf, (stepSystem base observes).LogicallyEquivalent C D ∧
        ¬ (stepSystem base observes).Bisimilar C D :=
  ⟨Option ℕ, tagView, tagView_invariant, rootAConf, rootBConf, roots_logicallyEquivalent,
    roots_not_bisimilar⟩

#print axioms ground_consistent_iff
#print axioms base_succ_iff
#print axioms succ_extends
#print axioms succ_tell
#print axioms sameKnowledge_isBisimulation
#print axioms knowledgeView_adequacy
#print axioms renamed_isBisimulation_base
#print axioms renamed_of_sameView
#print axioms storeView_adequacy_base
#print axioms tagView_program_adequacy
#print axioms shaped_of_append
#print axioms junk_isBisimulation
#print axioms tagged_sat_iff
#print axioms wit_sat_iff_tag
#print axioms roots_sat_iff
#print axioms roots_logicallyEquivalent
#print axioms rootB_reaches_wit
#print axioms roots_not_bisimilar
#print axioms unrestricted_adequacy_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.UnrestrictedStep
