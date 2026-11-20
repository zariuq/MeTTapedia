import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Controls

/-!
# One step up: the bisimilarity of a fixed program

A program is a set `R` of rule instances; its step is the program-free step restricted to the rules
of `R`, labelled by them (`programOffers`). Its successors are those of the step of
`ProgramAdequacy.program` (`program_succ_iff_moves`).

* **Containment** (`programBisimilar_of_bisimilar`, `programBisimilar_of_moduloEquivalent`):
  bisimilarity of the program-free step, hence equivalence modulo the knowledge with a fresh supply,
  is contained in the bisimilarity of every program.

## Take-and-make programs over a ground action

A rule **takes and makes** when it reads, tells and checks nothing (`TakeMake`). Over an action whose
substitutions fix every term and whose equality is syntactic (`GroundAction`), the knowledge of a
consistent configuration says nothing, and a configuration is read through its **bag** of labels.

* **What a word needs** (`need`): the least bag from which a word of rules fires;
  `need (ρ :: w) = take ρ ∪ (need w - make ρ + take ρ)`. A word of the program fires exactly when
  the bag holds what it needs (`hasTrace_iff`).
* **The characterization** (`takeMake_bisimilar_iff`): two consistent configurations are bisimilar
  for a take-and-make program exactly when every word of the program needs a bag below the first
  exactly when it needs a bag below the second. The invariant of the store is the set of words its
  bag affords.
* **Programs that take one row of one label** (`takeOne_bisimilar_iff`): bisimilar exactly when the
  configurations hold the same number of rows of that label.
* **Strictly coarser than equivalence modulo the knowledge** (`program_strictly_coarser`): for the
  finite program that takes one `T` at a time, on the tree's ground step, one row `T` and the rows
  `T, U` are bisimilar and not equivalent modulo the knowledge.

## Disjoint stores

* **The program whose one rule takes one row of one label and makes nothing composes**
  (`takeOne_tensor`): its bisimilarity is preserved by a disjoint store with consistent composites,
  since the numbers of rows of the label add up.
* **Every take-and-make program whose rules take at most one row each composes**, whatever they make
  (`oneTake_tensor`). A word fires from the composite exactly when it interleaves a word that fires
  from the system and a word that fires from the store: an interleaving of affordable words is
  affordable from the sum for every take-and-make word (`need_le_add_of_interleaves`), and when each
  rule takes at most one row, each firing takes its row from one part
  (`exists_interleaves_of_need_le_add`). An instance with a make: the program that takes `T` and
  makes `U`, on one row `T` against the rows `T, U`, beside another row `T` (`takeTmakeU_tensor`).
* **A two-row take does not** (`takeTU_not_congruence`): for the program that takes `T` and `U`
  together, one row `T` and no rows are bisimilar, and beside a disjoint row `U` they are not. The
  context brings the missing half of what the take needs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity

open AnnotatedRuns
open Semantic (ruleOffers FreshSupply)
open Observation (ModuloEquivalent)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uT uS uO

/-! ## The step of a program -/

section Program

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T} {C D : Configuration T O}

/-- **The step of a program**: the program-free step restricted to the rules of `R`, labelled by
them. -/
abbrev programOffers (A : SubstitutionAction T S) (R : Set (RuleInstance T)) :
    RuleInstance T → Firing T S O → Prop :=
  formOffers A (· ∈ R)

/-- **The successors of the program are those of `ProgramAdequacy.program`.** -/
theorem program_succ_iff_moves (R : Set (RuleInstance T)) (C C' : Configuration T O) :
    StepSpan.Succ (ProgramAdequacy.program A label R) C C' ↔
      ∃ ρ, Race.Moves A label (programOffers A R) C ρ C' := by
  rw [ProgramAdequacy.program_succ_iff]
  constructor
  · rintro ⟨ρ, selection, member, valid, rfl⟩
    exact ⟨ρ, moves_formOffers_iff.mpr ⟨member, moves_iff_step.mpr ⟨selection, valid, rfl⟩⟩⟩
  · rintro ⟨ρ, moved⟩
    obtain ⟨member, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨selection, valid, rfl⟩ := moves_iff_step.mp moved
    exact ⟨ρ, selection, member, valid, rfl⟩

/-- **Every program's bisimilarity contains the program-free bisimilarity.** -/
theorem programBisimilar_of_bisimilar (R : Set (RuleInstance T))
    (h : Race.Bisimilar A label (ruleOffers A) C D) :
    Race.Bisimilar A label (programOffers A R) C D :=
  bisimilar_formOffers h

/-- **Equivalence modulo the knowledge is contained in the bisimilarity of every program**, given a
fresh supply. -/
theorem programBisimilar_of_moduloEquivalent (supply : FreshSupply label) (R : Set (RuleInstance T))
    {E : Finset O} (h : ModuloEquivalent A label E C D) :
    Race.Bisimilar A label (programOffers A R) C D :=
  programBisimilar_of_bisimilar R (h.semantic_bisimilar supply)

end Program

/-! ## Take-and-make programs over a ground action -/

section TakeMake

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] [DecidableEq T]
  {A : SubstitutionAction T S} {label : O → T}

omit [DecidableEq T] in
/-- **A take-and-make rule**: it reads, tells and checks nothing. -/
def TakeMake (ρ : RuleInstance T) : Prop := ρ.read = [] ∧ ρ.tell = [] ∧ ρ.checks = []

omit [DecidableEq T] in
/-- **A ground action**: substitutions fix every term, and equality is syntactic. -/
structure GroundAction (A : SubstitutionAction T S) : Prop where
  fixes : ∀ σ t, A.apply σ t = t
  syntactic : ∀ s t, A.E s t ↔ s = t

omit [DecidableEq O] [DecidableEq T] in
variable (label) in
/-- **The bag of labels** of a configuration. -/
def bag (C : Configuration T O) : Multiset T := C.present.val.map label

/-- **What a word of rules needs**: the least bag from which it fires. -/
def need : List (RuleInstance T) → Multiset T
  | [] => 0
  | ρ :: w => (ρ.take : Multiset T) ∪ (need w - ρ.produce + ρ.take)

theorem need_cons_le_iff (ρ : RuleInstance T) (w : List (RuleInstance T)) (M : Multiset T) :
    need (ρ :: w) ≤ M ↔ (ρ.take : Multiset T) ≤ M ∧ need w ≤ M - ρ.take + ρ.produce := by
  show (ρ.take : Multiset T) ∪ (need w - ρ.produce + ρ.take) ≤ M ↔ _
  rw [Multiset.union_le_iff]
  refine and_congr_right fun enough => ?_
  constructor
  · intro rest
    exact tsub_le_iff_right.mp (le_tsub_of_add_le_right rest)
  · intro rest
    have below : need w - (ρ.produce : Multiset T) ≤ M - ρ.take := tsub_le_iff_right.mpr rest
    calc need w - (ρ.produce : Multiset T) + ρ.take ≤ M - ρ.take + ρ.take := add_le_add below le_rfl
      _ = M := tsub_add_cancel_of_le enough

theorem need_le_after_iff {ρ : RuleInstance T} {w : List (RuleInstance T)} {M : Multiset T}
    (enough : (ρ.take : Multiset T) ≤ M) :
    need w ≤ M - ρ.take + ρ.produce ↔ need (ρ :: w) ≤ M := by
  rw [need_cons_le_iff]
  exact ⟨fun rest => ⟨enough, rest⟩, fun both => both.2⟩

omit [DecidableEq O] [DecidableEq T] in
/-- **Matching equations over a ground action** hold exactly when the patterns are the labels. -/
theorem models_equations_ground (ground : GroundAction A) (σ : S) :
    ∀ (ps : List T) (taken : List O), ps.length = taken.length →
      (A.Models σ (Selection.equations label ps taken) ↔ ps = taken.map label)
  | [], [], _ => by simp [Selection.equations]
  | [], _ :: _, lengths => by simp at lengths
  | _ :: _, [], lengths => by simp at lengths
  | p :: ps, o :: taken, lengths => by
      have cons : Selection.equations label (p :: ps) (o :: taken) =
          (p, label o) :: Selection.equations label ps taken := rfl
      rw [cons, SubstitutionAction.models_cons,
        models_equations_ground ground σ ps taken (Nat.succ.inj lengths), List.map_cons,
        List.cons.injEq]
      show A.E (A.apply σ p) (A.apply σ (label o)) ∧ _ ↔ _
      rw [ground.fixes, ground.fixes, ground.syntactic]

omit [DecidableEq T] in
/-- **Distinct rows below a bag**: a list of labels below the bag of a set of rows is the list of
labels of distinct rows of the set. -/
theorem exists_taken : ∀ (ps : List T) (P : Finset O), (ps : Multiset T) ≤ P.val.map label →
    ∃ taken : List O, taken.Nodup ∧ (∀ o ∈ taken, o ∈ P) ∧ taken.map label = ps
  | [], _, _ => ⟨[], List.nodup_nil, fun _ member => absurd member List.not_mem_nil, rfl⟩
  | p :: ps, P, enough => by
      have member : p ∈ P.val.map label :=
        Multiset.mem_of_le enough (Multiset.mem_coe.mpr List.mem_cons_self)
      obtain ⟨o, inside, rfl⟩ := Multiset.mem_map.mp member
      have split : P.val.map label = label o ::ₘ (P.erase o).val.map label := by
        rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase inside]
      rw [split, ← Multiset.cons_coe, Multiset.cons_le_cons_iff] at enough
      obtain ⟨taken, nodup, within, mapped⟩ := exists_taken ps (P.erase o) enough
      refine ⟨o :: taken, List.nodup_cons.mpr
        ⟨fun inTaken => (Finset.mem_erase.mp (within o inTaken)).1 rfl, nodup⟩, ?_,
        by rw [List.map_cons, mapped]⟩
      intro x inList
      rcases List.mem_cons.mp inList with rfl | inTaken
      · exact Finset.mem_val.mp inside
      · exact (Finset.mem_erase.mp (within x inTaken)).2

/-- **The bag after a firing**: what was taken leaves, what was made arrives. -/
theorem bag_fire {P : Finset O} {taken made : List O} (nodup : taken.Nodup) (inside : ∀ o ∈ taken, o ∈ P)
    (madeNodup : made.Nodup) (fresh : Disjoint made.toFinset P) :
    ((P \ taken.toFinset) ∪ made.toFinset).val.map label =
      P.val.map label - ↑(taken.map label) + ↑(made.map label) := by
  have apart : Disjoint (P \ taken.toFinset) made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
  rw [← Finset.disjUnion_eq_union _ _ apart]
  show ((P \ taken.toFinset).val + made.toFinset.val).map label = _
  rw [Multiset.map_add, Finset.sdiff_val, List.toFinset_val, List.toFinset_val, nodup.dedup,
    madeNodup.dedup, Multiset.map_coe]
  congr 1
  have below : (taken : Multiset O) ≤ P.val :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr nodup)).mpr fun o inTaken =>
      Finset.mem_val.mpr (inside o (Multiset.mem_coe.mp inTaken))
  rw [← Multiset.map_coe]
  conv_rhs => rw [← tsub_add_cancel_of_le below]
  rw [Multiset.map_add, add_tsub_cancel_right]

/-- **A move of a take-and-make rule at a ground configuration**: the bag holds what the rule
takes, the new bag is the old one less what is taken plus what is made, and the knowledge stays
consistent. -/
theorem bag_of_moves (ground : GroundAction A) {ρ : RuleInstance T} (shape : TakeMake ρ)
    {C C' : Configuration T O} (moved : Race.Moves A label (ruleOffers A) C ρ C') :
    (ρ.take : Multiset T) ≤ bag label C ∧ bag label C' = bag label C - ρ.take + ρ.produce ∧
      A.Consistent C'.equations := by
  have consistent' := consistent_of_moves moved
  obtain ⟨⟨taken, read, made⟩, valid, rfl⟩ := moves_iff_step.mp moved
  have readNil : read = [] := by
    have lengths := valid.read_length
    rw [shape.1] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  subst readNil
  have mapped : ρ.take = taken.map label := by
    obtain ⟨σ, solved⟩ := valid.consistent
    have split := solved
    simp only [Selection.problem, SubstitutionAction.models_append] at split
    exact (models_equations_ground ground σ ρ.take taken valid.take_length).mp split.1.1.2
  have inside : ∀ o ∈ taken, o ∈ C.present := fun o member =>
    valid.occurrences.taken_subset (List.mem_toFinset.mpr member)
  have below : (taken : Multiset O) ≤ C.present.val :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr valid.take_distinct)).mpr fun o inTaken =>
      Finset.mem_val.mpr (inside o (Multiset.mem_coe.mp inTaken))
  refine ⟨?_, ?_, consistent'⟩
  · rw [mapped, ← Multiset.map_coe]
    exact Multiset.map_le_map below
  · show ((C.present \ taken.toFinset) ∪ made.toFinset).val.map label =
      C.present.val.map label - ρ.take + ρ.produce
    rw [bag_fire valid.take_distinct inside valid.output_distinct valid.occurrences.fresh, valid.outputs,
      mapped]

omit [DecidableEq T] in
/-- **A take-and-make rule moves wherever the bag holds what it takes**, over every action, given
consistent knowledge and a supply of fresh identities for every label. -/
theorem moves_of_le (supply : ProgramAdequacy.Supply label)
    {ρ : RuleInstance T} (shape : TakeMake ρ) {C : Configuration T O}
    (consistent : A.Consistent C.equations) (enough : (ρ.take : Multiset T) ≤ bag label C) :
    ∃ C', Race.Moves A label (ruleOffers A) C ρ C' := by
  obtain ⟨taken, nodup, inside, mapped⟩ := exists_taken ρ.take C.present enough
  obtain ⟨made, madeNodup, fresh, outputs⟩ := ProgramAdequacy.freshList label supply C.present ρ.produce
  have takes : ∀ σ, A.Models σ (Selection.equations label ρ.take taken) := fun σ => by
    rw [← mapped]
    exact models_self σ taken
  have valid : (⟨taken, [], made⟩ : Selection O).Valid A label ρ C := by
    refine ⟨nodup, madeNodup, by rw [← mapped, List.length_map], by rw [shape.1]; rfl, outputs,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro o member
      exact inside o (List.mem_toFinset.mp member)
    · simp [Selection.commit]
    · simp [Selection.commit]
    · exact Finset.disjoint_left.mpr fun o inMade inC => fresh o (List.mem_toFinset.mp inMade) inC
    · simp [Selection.commit]
    · obtain ⟨σ, solved⟩ := consistent
      refine ⟨σ, ?_⟩
      simp only [Selection.problem, SubstitutionAction.models_append, shape.2.1]
      exact ⟨⟨⟨solved, takes σ⟩, by simp [Selection.equations]⟩, A.models_nil σ⟩
    · intro check member
      rw [shape.2.2] at member
      cases member
  exact ⟨_, moves_iff_step.mpr ⟨_, valid, rfl⟩⟩

/-- **A word of the program fires exactly when the bag holds what it needs.** -/
theorem hasTrace_iff (ground : GroundAction A) (supply : ProgramAdequacy.Supply label)
    {R : Set (RuleInstance T)} (shape : ∀ ρ ∈ R, TakeMake ρ) :
    ∀ (w : List (RuleInstance T)) {C : Configuration T O}, A.Consistent C.equations →
      (Race.HasTrace A label (programOffers A R) w C ↔ (∀ ρ ∈ w, ρ ∈ R) ∧ need w ≤ bag label C)
  | [], C, _ =>
      ⟨fun _ => ⟨fun _ member => absurd member List.not_mem_nil, Multiset.zero_le _⟩,
        fun _ => Race.hasTrace_nil C⟩
  | ρ :: w, C, consistent => by
      rw [Race.hasTrace_cons]
      constructor
      · rintro ⟨C', moved, rest⟩
        obtain ⟨member, moved⟩ := moves_formOffers_iff.mp moved
        obtain ⟨enough, bagEq, consistent'⟩ := bag_of_moves ground (shape ρ member) moved
        obtain ⟨inR, needs⟩ := (hasTrace_iff ground supply shape w consistent').mp rest
        refine ⟨fun x inList => ?_, (need_le_after_iff enough).mp (by rw [← bagEq]; exact needs)⟩
        rcases List.mem_cons.mp inList with rfl | inW
        · exact member
        · exact inR x inW
      · rintro ⟨inR, needs⟩
        have member : ρ ∈ R := inR ρ List.mem_cons_self
        obtain ⟨enough, rest⟩ := (need_cons_le_iff ρ w _).mp needs
        obtain ⟨C', moved⟩ := moves_of_le supply (shape ρ member) consistent enough
        obtain ⟨-, bagEq, consistent'⟩ := bag_of_moves ground (shape ρ member) moved
        refine ⟨C', moves_formOffers_iff.mpr ⟨member, moved⟩,
          (hasTrace_iff ground supply shape w consistent').mpr ⟨fun x inW => inR x
            (List.mem_cons_of_mem ρ inW), by rw [bagEq]; exact rest⟩⟩

variable (A label) in
/-- **The same affordances**: both configurations are consistent, and every word of the program
needs a bag below the first exactly when it needs a bag below the second. -/
def SameAffordances (R : Set (RuleInstance T)) (X Y : Configuration T O) : Prop :=
  A.Consistent X.equations ∧ A.Consistent Y.equations ∧
    ∀ w : List (RuleInstance T), (∀ ρ ∈ w, ρ ∈ R) → (need w ≤ bag label X ↔ need w ≤ bag label Y)

/-- **Bisimilarity of a take-and-make program over a ground action**: two consistent configurations
are bisimilar exactly when every word of the program needs a bag below the first exactly when it
needs a bag below the second. -/
theorem takeMake_bisimilar_iff (ground : GroundAction A) (supply : ProgramAdequacy.Supply label)
    {R : Set (RuleInstance T)} (shape : ∀ ρ ∈ R, TakeMake ρ) {C D : Configuration T O}
    (consistentC : A.Consistent C.equations) (consistentD : A.Consistent D.equations) :
    Race.Bisimilar A label (programOffers A R) C D ↔
      ∀ w : List (RuleInstance T), (∀ ρ ∈ w, ρ ∈ R) →
        (need w ≤ bag label C ↔ need w ≤ bag label D) := by
  constructor
  · intro h w inR
    have traces := Race.traceEquivalent_of_bisimilar h w
    rw [hasTrace_iff ground supply shape w consistentC, hasTrace_iff ground supply shape w consistentD]
      at traces
    exact ⟨fun le => (traces.mp ⟨inR, le⟩).2, fun le => (traces.mpr ⟨inR, le⟩).2⟩
  · intro same
    have transfer : ∀ {X Y : Configuration T O}, SameAffordances A label R X Y →
        ∀ (ρ : RuleInstance T) (X' : Configuration T O),
          Race.Moves A label (programOffers A R) X ρ X' →
            ∃ Y', Race.Moves A label (programOffers A R) Y ρ Y' ∧ SameAffordances A label R X' Y' := by
      rintro X Y ⟨consistentX, consistentY, agree⟩ ρ X' moved
      obtain ⟨member, moved⟩ := moves_formOffers_iff.mp moved
      obtain ⟨enoughX, bagX, consistentX'⟩ := bag_of_moves ground (shape ρ member) moved
      have single : ∀ x ∈ [ρ], x ∈ R := fun x inList => by
        rw [List.mem_singleton.mp inList]
        exact member
      have enoughY : (ρ.take : Multiset T) ≤ bag label Y :=
        ((need_cons_le_iff ρ [] _).mp ((agree [ρ] single).mp
          ((need_cons_le_iff ρ [] _).mpr ⟨enoughX, Multiset.zero_le _⟩))).1
      obtain ⟨Y', movedY⟩ := moves_of_le supply (shape ρ member) consistentY enoughY
      obtain ⟨-, bagY, consistentY'⟩ := bag_of_moves ground (shape ρ member) movedY
      refine ⟨Y', moves_formOffers_iff.mpr ⟨member, movedY⟩, consistentX', consistentY',
        fun w inR => ?_⟩
      have cons : ∀ x ∈ ρ :: w, x ∈ R := fun x inList => by
        rcases List.mem_cons.mp inList with rfl | inW
        · exact member
        · exact inR x inW
      rw [bagX, bagY, need_le_after_iff enoughX, need_le_after_iff enoughY]
      exact agree (ρ :: w) cons
    have symmetric : ∀ {X Y : Configuration T O}, SameAffordances A label R X Y →
        SameAffordances A label R Y X :=
      fun related => ⟨related.2.1, related.1, fun w inR => (related.2.2 w inR).symm⟩
    refine ⟨SameAffordances A label R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
      consistentC, consistentD, same⟩
    · intro X Y related ρ X' moved
      exact transfer related ρ X' moved
    · intro X Y related ρ Y' moved
      obtain ⟨X', moved', related'⟩ := transfer (symmetric related) ρ Y' moved
      exact ⟨X', moved', symmetric related'⟩

/-- **What words of one take need**: a word of rules that each take one row `t` needs as many
copies of `t` as it is long. -/
theorem need_takeOne_le_iff (t : T) :
    ∀ (w : List (RuleInstance T)), (∀ ρ ∈ w, ρ = takeRule [t]) →
      ∀ M : Multiset T, need w ≤ M ↔ w.length ≤ M.count t
  | [], _, M => ⟨fun _ => Nat.zero_le _, fun _ => Multiset.zero_le _⟩
  | ρ :: w, each, M => by
      obtain rfl := each ρ List.mem_cons_self
      rw [need_cons_le_iff, need_takeOne_le_iff t w (fun x inW => each x (List.mem_cons_of_mem _ inW))]
      have takes : ((takeRule [t]).take : Multiset T) = {t} := by simp [takeRule]
      have makes : ((takeRule [t]).produce : Multiset T) = 0 := by simp [takeRule]
      rw [takes, makes, add_zero, Multiset.count_sub, Multiset.count_singleton_self,
        Multiset.singleton_le, ← Multiset.count_pos, List.length_cons]
      omega

/-- **Programs that take one row of one label**: two consistent configurations are bisimilar exactly
when they hold the same number of rows of that label. -/
theorem takeOne_bisimilar_iff (ground : GroundAction A) (supply : ProgramAdequacy.Supply label) (t : T)
    {C D : Configuration T O} (consistentC : A.Consistent C.equations)
    (consistentD : A.Consistent D.equations) :
    Race.Bisimilar A label (programOffers A {takeRule [t]}) C D ↔
      (bag label C).count t = (bag label D).count t := by
  rw [takeMake_bisimilar_iff ground supply (fun ρ member => by
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨rfl, rfl, rfl⟩) consistentC consistentD]
  constructor
  · intro agree
    have rule : ∀ n : ℕ, ∀ x ∈ List.replicate n (takeRule [t]), x = takeRule [t] :=
      fun _ _ inList => List.eq_of_mem_replicate inList
    have inR : ∀ n : ℕ, ∀ x ∈ List.replicate n (takeRule [t]), x ∈ ({takeRule [t]} : Set (RuleInstance T)) :=
      fun n x inList => Set.mem_singleton_iff.mpr (rule n x inList)
    have reads : ∀ (n : ℕ) (M : Multiset T),
        need (List.replicate n (takeRule [t])) ≤ M ↔ n ≤ M.count t := by
      intro n M
      rw [need_takeOne_le_iff t _ (rule n), List.length_replicate]
    have atC := agree _ (inR ((bag label C).count t))
    have atD := agree _ (inR ((bag label D).count t))
    rw [reads, reads] at atC
    rw [reads, reads] at atD
    exact le_antisymm (atC.mp le_rfl) (atD.mpr le_rfl)
  · intro counts w inR
    have rule : ∀ x ∈ w, x = takeRule [t] := fun x inW => Set.mem_singleton_iff.mp (inR x inW)
    rw [need_takeOne_le_iff t w rule, need_takeOne_le_iff t w rule, counts]

omit [DecidableEq T] in
/-- The bag of a disjoint composite is the sum of the bags. -/
theorem bag_tensor {C F : Configuration T O} (apart : Disjoint C.present F.present) :
    bag label (AnnotatedRuns.tensor C F) = bag label C + bag label F := by
  show (C.present ∪ F.present).val.map label = C.present.val.map label + F.present.val.map label
  rw [← Finset.disjUnion_eq_union _ _ apart]
  exact Multiset.map_add _ _ _

/-- **The program whose one rule takes one row of one label and makes nothing composes**: its
bisimilarity is preserved by a disjoint store with consistent composites, since the numbers of rows
of the label add up. -/
theorem takeOne_tensor (ground : GroundAction A) (supply : ProgramAdequacy.Supply label) (t : T)
    {C D F : Configuration T O} (h : Race.Bisimilar A label (programOffers A {takeRule [t]}) C D)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present)
    (consistentCF : A.Consistent (AnnotatedRuns.tensor C F).equations)
    (consistentDF : A.Consistent (AnnotatedRuns.tensor D F).equations) :
    Race.Bisimilar A label (programOffers A {takeRule [t]})
      (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  have left : ∀ {X : Configuration T O}, A.Consistent (AnnotatedRuns.tensor X F).equations →
      A.Consistent X.equations := by
    rintro X ⟨σ, solved⟩
    exact ⟨σ, ((A.models_append _ _ _).mp solved).1⟩
  have counts := (takeOne_bisimilar_iff ground supply t (left consistentCF) (left consistentDF)).mp h
  refine (takeOne_bisimilar_iff ground supply t consistentCF consistentDF).mpr ?_
  rw [bag_tensor apartC, bag_tensor apartD, Multiset.count_add, Multiset.count_add, counts]

/-- **Interleavings**: `w` interleaves `u` and `v`, keeping the order of each. -/
inductive Interleaves {α : Type*} : List α → List α → List α → Prop
  | nil : Interleaves [] [] []
  | left {a : α} {u v w : List α} : Interleaves u v w → Interleaves (a :: u) v (a :: w)
  | right {a : α} {u v w : List α} : Interleaves u v w → Interleaves u (a :: v) (a :: w)

/-- The words an interleaving interleaves are made of its letters. -/
theorem Interleaves.mem {α : Type*} {u v w : List α} (inter : Interleaves u v w) {a : α} :
    (a ∈ u → a ∈ w) ∧ (a ∈ v → a ∈ w) := by
  induction inter with
  | nil => exact ⟨id, id⟩
  | left _ ih =>
      refine ⟨fun inside => ?_, fun inside => List.mem_cons_of_mem _ (ih.2 inside)⟩
      rcases List.mem_cons.mp inside with rfl | later
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.1 later)
  | right _ ih =>
      refine ⟨fun inside => List.mem_cons_of_mem _ (ih.1 inside), fun inside => ?_⟩
      rcases List.mem_cons.mp inside with rfl | later
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.2 later)

/-- **An interleaving of affordable words is affordable from the sum**, for every take-and-make word:
what one part needs it takes from its own rows. -/
theorem need_le_add_of_interleaves {u v w : List (RuleInstance T)} (inter : Interleaves u v w) :
    ∀ {M N : Multiset T}, need u ≤ M → need v ≤ N → need w ≤ M + N := by
  induction inter with
  | nil => exact fun _ _ => Multiset.zero_le _
  | @left ρ u v w _ ih =>
      intro M N leftNeed rightNeed
      obtain ⟨enough, rest⟩ := (need_cons_le_iff ρ u M).mp leftNeed
      refine (need_cons_le_iff ρ w (M + N)).mpr ⟨le_trans enough (Multiset.le_add_right _ _), ?_⟩
      have shape : M + N - (ρ.take : Multiset T) + ρ.produce =
          M - (ρ.take : Multiset T) + ρ.produce + N := by
        rw [← tsub_add_eq_add_tsub enough, add_right_comm]
      rw [shape]
      exact ih rest rightNeed
  | @right ρ u v w _ ih =>
      intro M N leftNeed rightNeed
      obtain ⟨enough, rest⟩ := (need_cons_le_iff ρ v N).mp rightNeed
      refine (need_cons_le_iff ρ w (M + N)).mpr ⟨le_trans enough (Multiset.le_add_left _ _), ?_⟩
      have shape : M + N - (ρ.take : Multiset T) + ρ.produce =
          M + (N - (ρ.take : Multiset T) + ρ.produce) := by
        rw [add_tsub_assoc_of_le enough M, add_assoc]
      rw [shape]
      exact ih leftNeed rest

/-- **What the sum affords is interleavings of what the parts afford**, for words whose rules take at
most one row each: each firing takes its row from one part, and a rule that takes nothing goes with
the first part. -/
theorem exists_interleaves_of_need_le_add :
    ∀ (w : List (RuleInstance T)), (∀ ρ ∈ w, ρ.take.length ≤ 1) → ∀ {M N : Multiset T},
      need w ≤ M + N → ∃ u v, Interleaves u v w ∧ need u ≤ M ∧ need v ≤ N
  | [], _, _, _, _ => ⟨[], [], .nil, Multiset.zero_le _, Multiset.zero_le _⟩
  | ρ :: w, oneTake, M, N, needed => by
      obtain ⟨enough, rest⟩ := (need_cons_le_iff ρ w (M + N)).mp needed
      have restOne : ∀ σ ∈ w, σ.take.length ≤ 1 := fun σ inW => oneTake σ (List.mem_cons_of_mem _ inW)
      have short : ρ.take.length ≤ 1 := oneTake ρ List.mem_cons_self
      match taken : ρ.take, short with
      | [], _ =>
          have zero : (ρ.take : Multiset T) = 0 := by rw [taken, Multiset.coe_nil]
          have shape : M + N - (ρ.take : Multiset T) + ρ.produce = M + ρ.produce + N := by
            rw [zero, tsub_zero, add_right_comm]
          rw [shape] at rest
          obtain ⟨u, v, inter, needU, needV⟩ := exists_interleaves_of_need_le_add w restOne rest
          have nothing : (ρ.take : Multiset T) ≤ M := by
            rw [zero]
            exact Multiset.zero_le _
          have after : need u ≤ M - (ρ.take : Multiset T) + ρ.produce := by
            rw [zero, tsub_zero]
            exact needU
          exact ⟨ρ :: u, v, .left inter, (need_cons_le_iff ρ u M).mpr ⟨nothing, after⟩, needV⟩
      | [t], _ =>
          have single : (ρ.take : Multiset T) = {t} := by rw [taken, Multiset.coe_singleton]
          rw [single, Multiset.singleton_le, Multiset.mem_add] at enough
          rcases enough with inM | inN
          · have below : (ρ.take : Multiset T) ≤ M := by
              rw [single, Multiset.singleton_le]
              exact inM
            have shape : M + N - (ρ.take : Multiset T) + ρ.produce =
                M - (ρ.take : Multiset T) + ρ.produce + N := by
              rw [← tsub_add_eq_add_tsub below, add_right_comm]
            rw [shape] at rest
            obtain ⟨u, v, inter, needU, needV⟩ := exists_interleaves_of_need_le_add w restOne rest
            exact ⟨ρ :: u, v, .left inter, (need_cons_le_iff ρ u M).mpr ⟨below, needU⟩, needV⟩
          · have below : (ρ.take : Multiset T) ≤ N := by
              rw [single, Multiset.singleton_le]
              exact inN
            have shape : M + N - (ρ.take : Multiset T) + ρ.produce =
                M + (N - (ρ.take : Multiset T) + ρ.produce) := by
              rw [add_tsub_assoc_of_le below M, add_assoc]
            rw [shape] at rest
            obtain ⟨u, v, inter, needU, needV⟩ := exists_interleaves_of_need_le_add w restOne rest
            exact ⟨u, ρ :: v, .right inter, needU, (need_cons_le_iff ρ v N).mpr ⟨below, needV⟩⟩
      | _ :: _ :: _, tooLong => simp at tooLong

/-- **Take-and-make programs whose rules take at most one row each compose**: over a ground action
with a supply of fresh identities, their bisimilarity is preserved by a disjoint store with consistent
composites, whatever the rules make. A word fires from the composite exactly when it interleaves a
word that fires from the system and a word that fires from the store
(`exists_interleaves_of_need_le_add`, `need_le_add_of_interleaves`). With a rule that takes two rows
this fails (`takeTU_not_congruence`). -/
theorem oneTake_tensor (ground : GroundAction A) (supply : ProgramAdequacy.Supply label)
    {R : Set (RuleInstance T)} (shape : ∀ ρ ∈ R, TakeMake ρ) (oneTake : ∀ ρ ∈ R, ρ.take.length ≤ 1)
    {C D F : Configuration T O} (h : Race.Bisimilar A label (programOffers A R) C D)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present)
    (consistentCF : A.Consistent (AnnotatedRuns.tensor C F).equations)
    (consistentDF : A.Consistent (AnnotatedRuns.tensor D F).equations) :
    Race.Bisimilar A label (programOffers A R)
      (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  have left : ∀ {X : Configuration T O}, A.Consistent (AnnotatedRuns.tensor X F).equations →
      A.Consistent X.equations := by
    rintro X ⟨σ, solved⟩
    exact ⟨σ, ((A.models_append _ _ _).mp solved).1⟩
  have agree :=
    (takeMake_bisimilar_iff ground supply shape (left consistentCF) (left consistentDF)).mp h
  refine (takeMake_bisimilar_iff ground supply shape consistentCF consistentDF).mpr fun w inR => ?_
  rw [bag_tensor apartC, bag_tensor apartD]
  have transfer : ∀ {X Y : Configuration T O},
      (∀ u : List (RuleInstance T), (∀ ρ ∈ u, ρ ∈ R) → need u ≤ bag label X → need u ≤ bag label Y) →
        need w ≤ bag label X + bag label F → need w ≤ bag label Y + bag label F := by
    intro X Y imply needed
    obtain ⟨u, v, inter, needU, needV⟩ :=
      exists_interleaves_of_need_le_add w (fun ρ inW => oneTake ρ (inR ρ inW)) needed
    exact need_le_add_of_interleaves inter
      (imply u (fun ρ inU => inR ρ (inter.mem.1 inU)) needU) needV
  exact ⟨transfer fun u inU => (agree u inU).mp, transfer fun u inU => (agree u inU).mpr⟩

end TakeMake

/-! ## Strictly coarser: one take of `T` on the tree's ground step -/

section Coarser

open NamesOnTheStep.IssuingControls (ground Occ Conf factT factU)

theorem issuing_ground : GroundAction ground := ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

/-- One row `T`. -/
def oneT : Conf := ⟨[], {(factT, 0)}⟩

/-- The rows `T` and `U`. -/
def oneTU : Conf := ⟨[], {(factT, 0), (factU, 0)}⟩

/-- **For a fixed finite program, bisimilarity is strictly coarser than equivalence modulo the
knowledge**: the program that takes one `T` at a time cannot see the row `U`. -/
theorem program_strictly_coarser :
    ({takeRule [factT]} : Set (RuleInstance NamesOnTheStep.Expr)).Finite ∧
      Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr)
        (programOffers ground {takeRule [factT]}) oneT oneTU ∧
      ¬ (∃ E, ModuloEquivalent ground (Prod.fst : Occ → NamesOnTheStep.Expr) E oneT oneTU) := by
  refine ⟨Set.finite_singleton _, ?_, fun ⟨E, h⟩ => absurd h.card_eq (by decide)⟩
  refine (takeOne_bisimilar_iff issuing_ground ProgramAdequacy.occSupply factT
    ⟨(), ground.models_nil _⟩ ⟨(), ground.models_nil _⟩).mpr ?_
  decide

/-- Another row `T`, disjoint from both. -/
def otherT : Conf := ⟨[], {(factT, 1)}⟩

/-- **The program that takes one `T` composes, on the pair above**: beside another row `T` they stay
bisimilar. -/
theorem program_strictly_coarser_tensor :
    Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr) (programOffers ground {takeRule [factT]})
      (AnnotatedRuns.tensor oneT otherT) (AnnotatedRuns.tensor oneTU otherT) :=
  takeOne_tensor issuing_ground ProgramAdequacy.occSupply factT program_strictly_coarser.2.1
    (by decide) (by decide) ⟨(), ground.models_nil _⟩ ⟨(), ground.models_nil _⟩

/-- The rule that takes `T` and `U` together. -/
def takeTU : RuleInstance NamesOnTheStep.Expr := takeRule [factT, factU]

/-- One row `U`. -/
def oneU : Conf := ⟨[], {(factU, 0)}⟩

/-- No rows. -/
def noRows : Conf := ⟨[], ∅⟩

/-- **Fewer than two rows cannot take `T` and `U` together.** -/
theorem takeTU_halted {X : Conf} (small : X.present.card ≤ 1) (ρ : RuleInstance NamesOnTheStep.Expr)
    (X' : Conf) : ¬ Race.Moves ground (Prod.fst : Occ → NamesOnTheStep.Expr)
      (programOffers ground {takeTU}) X ρ X' := by
  intro moved
  obtain ⟨member, moved⟩ := moves_formOffers_iff.mp moved
  rw [Set.mem_singleton_iff.mp member] at moved
  obtain ⟨taken, nodup, lengths, inside, -, -⟩ := moves_take_iff.mp moved
  have counted := Finset.card_le_card
    (show taken.toFinset ⊆ X.present from fun o inList => inside o (List.mem_toFinset.mp inList))
  rw [List.toFinset_card_of_nodup nodup, ← lengths] at counted
  simp only [List.length_cons, List.length_nil] at counted
  omega

/-- **Bisimilarity of a take-and-make program is not a congruence for disjoint stores**: for the
program that takes `T` and `U` together, one row `T` and no rows are bisimilar (neither moves), and
beside the disjoint row `U` they are not (only the first composite can take both). Programs whose rules
take at most one row each compose (`oneTake_tensor`); a two-row take needs what a context may bring. -/
theorem takeTU_not_congruence :
    Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr) (programOffers ground {takeTU})
        oneT noRows ∧
      Disjoint oneT.present oneU.present ∧ Disjoint noRows.present oneU.present ∧
      ¬ Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr) (programOffers ground {takeTU})
        (AnnotatedRuns.tensor oneT oneU) (AnnotatedRuns.tensor noRows oneU) := by
  refine ⟨Race.bisimilar_of_halted (takeTU_halted (by decide)) (takeTU_halted (by decide)),
    by decide, by decide, ?_⟩
  refine Race.not_bisimilar_of_sat (φ := .dia takeTU .top) (Race.sat_dia.mpr ⟨_,
    moves_formOffers_iff.mpr ⟨Set.mem_singleton _, moves_take_iff.mpr ⟨[(factT, 0), (factU, 0)],
      by decide, rfl, by decide, ⟨(), (ground.models_append _ _ _).mpr ⟨ground.models_nil _,
        models_self () [(factT, 0), (factU, 0)]⟩⟩, rfl⟩⟩, Race.sat_top _⟩) ?_
  rintro ⟨X', moved, -⟩
  exact takeTU_halted (by decide) takeTU X' moved

/-- The rule that takes `T` and makes `U`. -/
def takeTmakeU : RuleInstance NamesOnTheStep.Expr := ⟨[factT], [], [], [], [factU]⟩

/-- **What words of `takeTmakeU` need**: as many rows `T` as they are long; the `U` they make is never
taken. -/
theorem need_takeTmakeU_le_iff :
    ∀ (w : List (RuleInstance NamesOnTheStep.Expr)), (∀ ρ ∈ w, ρ = takeTmakeU) →
      ∀ M : Multiset NamesOnTheStep.Expr, need w ≤ M ↔ w.length ≤ M.count factT
  | [], _, M => ⟨fun _ => Nat.zero_le _, fun _ => Multiset.zero_le _⟩
  | ρ :: w, each, M => by
      obtain rfl := each ρ List.mem_cons_self
      rw [need_cons_le_iff,
        need_takeTmakeU_le_iff w (fun x inW => each x (List.mem_cons_of_mem _ inW))]
      have takes : (takeTmakeU.take : Multiset NamesOnTheStep.Expr) = {factT} := by
        simp [takeTmakeU]
      have makes : (takeTmakeU.produce : Multiset NamesOnTheStep.Expr) = {factU} := by
        simp [takeTmakeU]
      have different : factT ≠ factU := by decide
      rw [takes, makes, Multiset.count_add, Multiset.count_sub, Multiset.count_singleton_self,
        Multiset.count_singleton, if_neg different, Multiset.singleton_le, ← Multiset.count_pos,
        List.length_cons]
      omega

/-- **A one-row take with a make composes, an instance of `oneTake_tensor`**: for the program that
takes `T` and makes `U`, one row `T` and the rows `T, U` are bisimilar (the `U` is never taken), and
they stay bisimilar beside another row `T`. -/
theorem takeTmakeU_tensor :
    Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr) (programOffers ground {takeTmakeU})
        oneT oneTU ∧
      Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr) (programOffers ground {takeTmakeU})
        (AnnotatedRuns.tensor oneT otherT) (AnnotatedRuns.tensor oneTU otherT) := by
  have shape : ∀ ρ ∈ ({takeTmakeU} : Set (RuleInstance NamesOnTheStep.Expr)), TakeMake ρ := by
    intro ρ member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨rfl, rfl, rfl⟩
  have oneTake : ∀ ρ ∈ ({takeTmakeU} : Set (RuleInstance NamesOnTheStep.Expr)),
      ρ.take.length ≤ 1 := by
    intro ρ member
    rw [Set.mem_singleton_iff.mp member]
    exact Nat.le_refl _
  have pair : Race.Bisimilar ground (Prod.fst : Occ → NamesOnTheStep.Expr)
      (programOffers ground {takeTmakeU}) oneT oneTU := by
    refine (takeMake_bisimilar_iff issuing_ground ProgramAdequacy.occSupply shape
      ⟨(), ground.models_nil _⟩ ⟨(), ground.models_nil _⟩).mpr fun w inR => ?_
    have each : ∀ ρ ∈ w, ρ = takeTmakeU := fun ρ inW => Set.mem_singleton_iff.mp (inR ρ inW)
    rw [need_takeTmakeU_le_iff w each, need_takeTmakeU_le_iff w each]
    have same : (bag (Prod.fst : Occ → NamesOnTheStep.Expr) oneT).count factT =
        (bag (Prod.fst : Occ → NamesOnTheStep.Expr) oneTU).count factT := by
      decide
    rw [same]
  exact ⟨pair, oneTake_tensor issuing_ground ProgramAdequacy.occSupply shape oneTake pair
    (by decide) (by decide) ⟨(), ground.models_nil _⟩ ⟨(), ground.models_nil _⟩⟩

end Coarser

#print axioms program_succ_iff_moves
#print axioms programBisimilar_of_bisimilar
#print axioms programBisimilar_of_moduloEquivalent
#print axioms need_cons_le_iff
#print axioms models_equations_ground
#print axioms exists_taken
#print axioms bag_fire
#print axioms bag_of_moves
#print axioms moves_of_le
#print axioms hasTrace_iff
#print axioms takeMake_bisimilar_iff
#print axioms need_takeOne_le_iff
#print axioms takeOne_bisimilar_iff
#print axioms bag_tensor
#print axioms takeOne_tensor
#print axioms Interleaves.mem
#print axioms need_le_add_of_interleaves
#print axioms exists_interleaves_of_need_le_add
#print axioms oneTake_tensor
#print axioms program_strictly_coarser
#print axioms program_strictly_coarser_tensor
#print axioms takeTU_halted
#print axioms takeTU_not_congruence
#print axioms need_takeTmakeU_le_iff
#print axioms takeTmakeU_tensor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity
