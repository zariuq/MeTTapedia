import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsTensor

/-!
# The separation algebra of configurations

Configurations of the candidate step compose by the tensor of `AnnotatedRunsTensor`: both stores
of equations, both sets of occurrences. Two configurations are **separable** (`Separable`) when
their occurrences are disjoint and their equations are compatible: the joint store has a solution.

## A partial commutative monoid

* On configurations the laws hold up to classes (`separable_comm`, `separable_assoc`,
  `separable_unit_right`, with `tensor_assoc`, `tensor_comm` and the units of
  `AnnotatedRunsTensor`); separability and the tensor respect classes (`separable_congr`,
  `tensor_congr`).
* On configuration classes the join relation `JoinClass x y z` is a separation algebra in the
  relational form of Dockins, Hobor and Appel: functional (`joinClass_functional`), commutative
  (`joinClass_comm`), associative (`joinClass_assoc`), with the empty configuration as a unit of
  every class that has a solution (`joinClass_unit_iff`).

## Two kinds of resource

Every configuration is its knowledge beside its occurrences (`decompose`). Occurrences are
**exclusive**: a configuration is separable from itself only when it has none
(`separable_self_iff`). Knowledge is **duplicable**: a store composed with itself has the same
solutions (`knowledge_duplicable`). This is the split of the linear-logic reading of Constraint
Handling Rules, where user constraints are linear and built-in constraints are under `!`.

## Cancellativity

* Occurrences cancel (`present_cancel`), and so does the syntax of configurations
  (`tensor_cancel`): from `C ⊗ D = C ⊗ D'` with disjoint occurrences, `D = D'`.
* Classes cancel only relative to what the cancelled part knows (`tensor_sameUpTo_cancel_iff`):
  `C ⊗ D` and `C ⊗ D'` are one class exactly when `D` and `D'` have the same occurrences and the
  same solutions among the solutions of `C`. Knowledge composed with itself is the negative
  control (`SeparationControls.classes_not_cancellative`).

## The partial tensor of runs

* **Separated runs are runs whose stages are pairwise separable** (`separated_iff_stages`): R26's
  `Separated` holds exactly when both runs execute, each is blind to the other's space, and every
  stage of the one is separable from every stage of the other. The space of a run is the union of
  its stages (`mem_space_iff_stage`).
* **`tensor_defined_iff` is separability of the ends** (`tensor_defined_iff_separable_ends`): for
  runs with disjoint spaces that are blind to each other, the tensor run is defined exactly when
  the configurations the two runs leave are separable. For empty runs this is separability itself
  (`tensor_nil_iff_separable`). Separable starts and separable ends are not enough without
  disjoint spaces: a run that makes and then takes an identity held by the other side
  (`SeparationControls.ends_separable_not_tensor`).
* **Unique splitting** (`tensor_split_unique`): when every firing of the second halves takes or
  reads an occurrence, a word splits into two separated runs from given halves in only one way. A
  firing that takes and reads nothing, such as a tell, splits two ways
  (`SeparationControls.tell_splits_two_ways`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire fire_union_frame)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

namespace SeparationRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Separability -/

section Algebra

variable (A : SubstitutionAction T S)

/-- **Two configurations are separable**: their occurrences are disjoint and their joint store has
a solution. -/
def Separable (C D : Configuration T O) : Prop :=
  Disjoint C.present D.present ∧ A.Consistent (C.equations ++ D.equations)

omit [DecidableEq O] in
theorem consistent_append_left {one two : EquationStore T} (consistent : A.Consistent (one ++ two)) :
    A.Consistent one := by
  obtain ⟨σ, solved⟩ := consistent
  exact ⟨σ, ((A.models_append σ one two).mp solved).1⟩

omit [DecidableEq O] in
theorem consistent_append_right {one two : EquationStore T}
    (consistent : A.Consistent (one ++ two)) : A.Consistent two := by
  obtain ⟨σ, solved⟩ := consistent
  exact ⟨σ, ((A.models_append σ one two).mp solved).2⟩

omit [DecidableEq O] in
theorem consistent_append_comm {one two : EquationStore T} :
    A.Consistent (one ++ two) ↔ A.Consistent (two ++ one) := by
  constructor
  · rintro ⟨σ, solved⟩
    exact ⟨σ, (A.models_append σ two one).mpr ((A.models_append σ one two).mp solved).symm⟩
  · rintro ⟨σ, solved⟩
    exact ⟨σ, (A.models_append σ one two).mpr ((A.models_append σ two one).mp solved).symm⟩

omit [DecidableEq O] in
/-- **Separability is symmetric.** -/
theorem separable_comm {C D : Configuration T O} : Separable A C D ↔ Separable A D C :=
  ⟨fun sep => ⟨sep.1.symm, (consistent_append_comm A).mp sep.2⟩,
    fun sep => ⟨sep.1.symm, (consistent_append_comm A).mp sep.2⟩⟩

/-- **Associativity of definedness**: the two bracketings of three configurations are defined
together. -/
theorem separable_assoc {C D E : Configuration T O} :
    (Separable A C D ∧ Separable A (tensor C D) E) ↔
      (Separable A D E ∧ Separable A C (tensor D E)) := by
  constructor
  · rintro ⟨⟨cd, _⟩, ⟨cde, joint⟩⟩
    have joint' : A.Consistent (C.equations ++ (D.equations ++ E.equations)) := by
      simpa [tensor, List.append_assoc] using joint
    have parts := Finset.disjoint_union_left.mp cde
    exact ⟨⟨parts.2, consistent_append_right A joint'⟩,
      ⟨Finset.disjoint_union_right.mpr ⟨cd, parts.1⟩, joint'⟩⟩
  · rintro ⟨⟨de, _⟩, ⟨cde, joint⟩⟩
    have joint' : A.Consistent ((C.equations ++ D.equations) ++ E.equations) := by
      simpa [tensor, List.append_assoc] using joint
    have parts := Finset.disjoint_union_right.mp cde
    exact ⟨⟨parts.1, consistent_append_left A joint'⟩,
      ⟨Finset.disjoint_union_left.mpr ⟨parts.2, de⟩, joint'⟩⟩

omit [DecidableEq O] in
/-- **The empty configuration is a unit for every configuration with a solution.** -/
theorem separable_unit_right (C : Configuration T O) :
    Separable A C unitConfiguration ↔ A.Consistent C.equations := by
  simp [Separable, unitConfiguration]

omit [DecidableEq O] in
theorem separable_unit_left (C : Configuration T O) :
    Separable A unitConfiguration C ↔ A.Consistent C.equations :=
  (separable_comm A).trans (separable_unit_right A C)

/-- The tensor respects classes. -/
theorem tensor_congr {C C' D D' : Configuration T O} (c : SameUpTo A C C') (d : SameUpTo A D D') :
    SameUpTo A (tensor C D) (tensor C' D') := by
  refine ⟨fun σ => ?_, ?_⟩
  · change A.Models σ (C.equations ++ D.equations) ↔ A.Models σ (C'.equations ++ D'.equations)
    rw [A.models_append, A.models_append, c.1 σ, d.1 σ]
  · change C.present ∪ D.present = C'.present ∪ D'.present
    rw [c.2, d.2]

/-- Separability respects classes. -/
theorem separable_congr {C C' D D' : Configuration T O} (c : SameUpTo A C C') (d : SameUpTo A D D') :
    Separable A C D ↔ Separable A C' D' := by
  unfold Separable
  rw [c.2, d.2]
  exact and_congr Iff.rfl (SubstitutionAction.equivalent_consistent A (tensor_congr A c d).1)

/-- The tensor of separable configurations has a solution. -/
theorem Separable.consistent {C D : Configuration T O} (sep : Separable A C D) :
    A.Consistent (tensor C D).equations :=
  sep.2

end Algebra

/-! ## Knowledge and occurrences -/

section Resources

variable (A : SubstitutionAction T S)

/-- A configuration of knowledge only. -/
def knowledge (K : EquationStore T) : Configuration T O := ⟨K, ∅⟩

/-- A configuration of occurrences only. -/
def spatial (P : Finset O) : Configuration T O := ⟨[], P⟩

/-- **Every configuration is its knowledge beside its occurrences.** -/
theorem decompose (C : Configuration T O) :
    tensor (knowledge C.equations) (spatial C.present) = ⟨C.equations ++ [], ∅ ∪ C.present⟩ :=
  rfl

theorem decompose_sameUpTo (C : Configuration T O) :
    SameUpTo A (tensor (knowledge C.equations) (spatial C.present)) C := by
  rw [decompose]
  exact ⟨fun σ => by rw [List.append_nil], Finset.empty_union _⟩

omit [DecidableEq O] in
theorem decompose_separable {C : Configuration T O} (consistent : A.Consistent C.equations) :
    Separable A (knowledge C.equations) (spatial C.present : Configuration T O) :=
  ⟨Finset.disjoint_empty_left _, by simpa [knowledge, spatial] using consistent⟩

omit [DecidableEq O] in
/-- **Occurrences are exclusive and knowledge is duplicable**: a configuration is separable from
itself exactly when it has no occurrence and its store has a solution. -/
theorem separable_self_iff (C : Configuration T O) :
    Separable A C C ↔ C.present = ∅ ∧ A.Consistent C.equations := by
  unfold Separable
  rw [Finset.disjoint_self_iff_empty]
  refine and_congr Iff.rfl ⟨consistent_append_left A, fun consistent => ?_⟩
  obtain ⟨σ, solved⟩ := consistent
  exact ⟨σ, (A.models_append σ _ _).mpr ⟨solved, solved⟩⟩

/-- **Knowledge composed with itself is itself.** -/
theorem knowledge_duplicable {K : EquationStore T} (consistent : A.Consistent K) :
    Separable A (knowledge K) (knowledge K : Configuration T O) ∧
      SameUpTo A (tensor (knowledge K) (knowledge K)) (knowledge K : Configuration T O) := by
  refine ⟨(separable_self_iff A _).mpr ⟨rfl, consistent⟩, fun σ => ?_, Finset.empty_union _⟩
  change A.Models σ (K ++ K) ↔ A.Models σ K
  rw [A.models_append, and_self]

omit [DecidableEq O] in
/-- **One occurrence on both sides is never separable.** -/
theorem not_separable_of_mem {C D : Configuration T O} {o : O} (inC : o ∈ C.present)
    (inD : o ∈ D.present) : ¬ Separable A C D :=
  fun sep => Finset.disjoint_left.mp sep.1 inC inD

end Resources

/-! ## Cancellativity -/

section Cancel

variable (A : SubstitutionAction T S)

/-- **Occurrences cancel.** -/
theorem present_cancel {P Q Q' : Finset O} (apart : Disjoint P Q) (apart' : Disjoint P Q')
    (same : P ∪ Q = P ∪ Q') : Q = Q' := by
  ext o
  constructor
  · intro inQ
    have inUnion : o ∈ P ∪ Q' := by rw [← same]; exact Finset.mem_union_right _ inQ
    rcases Finset.mem_union.mp inUnion with inP | inQ'
    · exact absurd inQ (Finset.disjoint_left.mp apart inP)
    · exact inQ'
  · intro inQ'
    have inUnion : o ∈ P ∪ Q := by rw [same]; exact Finset.mem_union_right _ inQ'
    rcases Finset.mem_union.mp inUnion with inP | inQ
    · exact absurd inQ' (Finset.disjoint_left.mp apart' inP)
    · exact inQ

omit [DecidableEq O] in
theorem configuration_ext {C D : Configuration T O} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  obtain ⟨e, p⟩ := C
  obtain ⟨e', p'⟩ := D
  dsimp only at equations present
  subst equations
  subst present
  rfl

/-- **The syntax of configurations cancels**: lists of equations cancel on the left, and disjoint
occurrences cancel. -/
theorem tensor_cancel {C D D' : Configuration T O} (apart : Disjoint C.present D.present)
    (apart' : Disjoint C.present D'.present) (same : tensor C D = tensor C D') : D = D' :=
  configuration_ext (List.append_cancel_left (congrArg Configuration.equations same))
    (present_cancel apart apart' (congrArg Configuration.present same))

/-- **Classes cancel only relative to the cancelled part's knowledge.** `C ⊗ D` and `C ⊗ D'` are
one class exactly when `D` and `D'` have the same occurrences and agree on the solutions of `C`. -/
theorem tensor_sameUpTo_cancel_iff {C D D' : Configuration T O} (apart : Disjoint C.present D.present)
    (apart' : Disjoint C.present D'.present) :
    SameUpTo A (tensor C D) (tensor C D') ↔
      D.present = D'.present ∧
        ∀ σ, A.Models σ C.equations → (A.Models σ D.equations ↔ A.Models σ D'.equations) := by
  constructor
  · rintro ⟨models, present⟩
    refine ⟨present_cancel apart apart' present, fun σ solvesC => ?_⟩
    have one := models σ
    change A.Models σ (C.equations ++ D.equations) ↔ A.Models σ (C.equations ++ D'.equations) at one
    rw [A.models_append, A.models_append] at one
    exact ⟨fun solvesD => (one.mp ⟨solvesC, solvesD⟩).2,
      fun solvesD' => (one.mpr ⟨solvesC, solvesD'⟩).2⟩
  · rintro ⟨present, agree⟩
    refine ⟨fun σ => ?_, ?_⟩
    · change A.Models σ (C.equations ++ D.equations) ↔ A.Models σ (C.equations ++ D'.equations)
      rw [A.models_append, A.models_append]
      exact ⟨fun ⟨c, d⟩ => ⟨c, (agree σ c).mp d⟩, fun ⟨c, d⟩ => ⟨c, (agree σ c).mpr d⟩⟩
    · change C.present ∪ D.present = C.present ∪ D'.present
      rw [present]

end Cancel

/-! ## Configuration classes form a separation algebra -/

section Classes

variable (A : SubstitutionAction T S)

omit [DecidableEq O] in
/-- A class whose stores have a solution. -/
def Live (x : ConfigurationClass A O) : Prop :=
  Quotient.lift (s := sameSetoid A) (fun C : Configuration T O => A.Consistent C.equations)
    (fun _ _ (same : SameUpTo A _ _) =>
      propext (SubstitutionAction.equivalent_consistent A same.1)) x

/-- **The join relation of classes**: `z` is the tensor of separable representatives of `x` and
`y`. -/
def JoinClass (x y z : ConfigurationClass A O) : Prop :=
  ∃ C D : Configuration T O, ConfigurationClass.mk A C = x ∧ ConfigurationClass.mk A D = y ∧
    Separable A C D ∧ ConfigurationClass.mk A (tensor C D) = z

/-- **Functionality.** -/
theorem joinClass_functional {x y z z' : ConfigurationClass A O} (join : JoinClass A x y z)
    (join' : JoinClass A x y z') : z = z' := by
  obtain ⟨C, D, hx, hy, -, hz⟩ := join
  obtain ⟨C', D', hx', hy', -, hz'⟩ := join'
  rw [← hz, ← hz']
  exact Quotient.sound (tensor_congr A (Quotient.exact (hx.trans hx'.symm))
    (Quotient.exact (hy.trans hy'.symm)))

/-- **Commutativity.** -/
theorem joinClass_comm {x y z : ConfigurationClass A O} (join : JoinClass A x y z) :
    JoinClass A y x z := by
  obtain ⟨C, D, hx, hy, sep, hz⟩ := join
  exact ⟨D, C, hy, hx, (separable_comm A).mp sep,
    (Quotient.sound (tensor_comm A D C)).trans hz⟩

/-- **Associativity.** -/
theorem joinClass_assoc {x y w xy z : ConfigurationClass A O} (first : JoinClass A x y xy)
    (second : JoinClass A xy w z) : ∃ yw, JoinClass A y w yw ∧ JoinClass A x yw z := by
  obtain ⟨C, D, hx, hy, sepCD, hxy⟩ := first
  obtain ⟨CD, E, hxy', hw, sepCDE, hz⟩ := second
  have same : SameUpTo A CD (tensor C D) := Quotient.exact (hxy'.trans hxy.symm)
  have sep' : Separable A (tensor C D) E :=
    (separable_congr A same (SameUpTo.refl A E)).mp sepCDE
  obtain ⟨sepDE, sepCDE'⟩ := (separable_assoc A).mp ⟨sepCD, sep'⟩
  refine ⟨ConfigurationClass.mk A (tensor D E), ⟨D, E, hy, hw, sepDE, rfl⟩,
    ⟨C, tensor D E, hx, rfl, sepCDE', ?_⟩⟩
  rw [← hz, ← tensor_assoc]
  exact Quotient.sound (tensor_congr A (sameUpTo_symm A same) (SameUpTo.refl A E))

/-- **The unit**: the empty configuration joins a class to itself exactly when the class has a
solution. -/
theorem joinClass_unit_iff (x : ConfigurationClass A O) :
    JoinClass A x (ConfigurationClass.mk A unitConfiguration) x ↔ Live A x := by
  constructor
  · rintro ⟨C, D, rfl, -, sep, -⟩
    exact consistent_append_left A sep.2
  · intro live
    obtain ⟨C, rfl⟩ := Quotient.exists_rep x
    refine ⟨C, unitConfiguration, rfl, rfl, (separable_unit_right A C).mpr live, ?_⟩
    show ConfigurationClass.mk A (tensor C unitConfiguration) = ConfigurationClass.mk A C
    rw [tensor_unit_right]

/-- **Knowledge joins with itself.** -/
theorem joinClass_knowledge_self {K : EquationStore T} (consistent : A.Consistent K) :
    JoinClass A (ConfigurationClass.mk A (knowledge K : Configuration T O))
      (ConfigurationClass.mk A (knowledge K : Configuration T O))
      (ConfigurationClass.mk A (knowledge K : Configuration T O)) := by
  obtain ⟨sep, same⟩ := knowledge_duplicable (O := O) A consistent
  exact ⟨knowledge K, knowledge K, rfl, rfl, sep, Quotient.sound same⟩

end Classes

/-! ## Stages of a run and the partial tensor -/

section Stages

variable (A : SubstitutionAction T S) (label : O → T)

/-- What a run leaves lies in its space. -/
theorem follow_present_subset_space : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    (follow label C w).present ⊆ space C w
  | _, [] => Finset.subset_union_left
  | C, f :: w => (follow_present_subset_space (f.result label C) w).trans
      (space_result_subset label f C w)

/-- A prefix has a smaller space. -/
theorem space_mono_prefix {C : Configuration T O} {u w : List (Firing T S O)} (prefix_ : u <+: w) :
    space C u ⊆ space C w := by
  obtain ⟨t, rfl⟩ := prefix_
  intro o member
  rcases Finset.mem_union.mp member with present | made
  · exact Finset.mem_union_left _ present
  · exact Finset.mem_union_right _ (by rw [madeBy_append]; exact Finset.mem_union_left _ made)

/-- **The space of a run is the union of its stages.** -/
theorem mem_space_iff_stage : ∀ (C : Configuration T O) (w : List (Firing T S O)) (o : O),
    o ∈ space C w ↔ ∃ u, u <+: w ∧ o ∈ (follow label C u).present
  | C, [], o => by
      constructor
      · intro member
        refine ⟨[], List.prefix_refl _, ?_⟩
        rcases Finset.mem_union.mp member with present | made
        · exact present
        · simp [madeBy] at made
      · rintro ⟨u, prefix_, member⟩
        exact space_mono_prefix prefix_ (follow_present_subset_space label C u member)
  | C, f :: w, o => by
      constructor
      · intro member
        rcases Finset.mem_union.mp member with present | made
        · exact ⟨[], List.nil_prefix, present⟩
        · rw [madeBy_cons] at made
          rcases Finset.mem_union.mp made with byF | later
          · refine ⟨[f], ⟨w, rfl⟩, ?_⟩
            change o ∈ fire C.present (f.selection.commit (T := T))
            exact mem_fire.mpr (Or.inr (by simpa [Selection.commit] using byF))
          · obtain ⟨u, ⟨t, rfl⟩, inStage⟩ :=
              (mem_space_iff_stage (f.result label C) w o).mp (Finset.mem_union_right _ later)
            exact ⟨f :: u, ⟨t, rfl⟩, inStage⟩
      · rintro ⟨u, prefix_, member⟩
        exact space_mono_prefix prefix_ (follow_present_subset_space label C u member)

omit [DecidableEq O] in
/-- The store a prefix leaves is solved by every solution of the whole run's added equations. -/
theorem models_prefix_added {σ : S} {u w : List (Firing T S O)} (prefix_ : u <+: w)
    (solved : A.Models σ (w.flatMap (Firing.added label))) :
    A.Models σ (u.flatMap (Firing.added label)) := by
  obtain ⟨t, rfl⟩ := prefix_
  rw [List.flatMap_append, A.models_append] at solved
  exact solved.1

/-- The joint store of two runs has the solutions of the two stores they leave. -/
theorem jointStore_equivalent (C₁ : Configuration T O) (r₁ : List (Firing T S O))
    (C₂ : Configuration T O) (r₂ : List (Firing T S O)) :
    A.Equivalent (jointStore label C₁ r₁ C₂ r₂)
      ((follow label C₁ r₁).equations ++ (follow label C₂ r₂).equations) := by
  intro σ
  rw [models_jointStore, A.models_append, follow_equations, follow_equations, A.models_append,
    A.models_append]
  tauto

/-- **Separated runs are runs whose stages are pairwise separable.** R26's `Separated` holds
exactly when both runs execute, each is blind to the other's space, and every stage of the one is
separable from every stage of the other. -/
theorem separated_iff_stages {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)} :
    Separated A label C₁ r₁ C₂ r₂ ↔
      Executable A label C₁ r₁ ∧ Executable A label C₂ r₂ ∧
        (∀ f ∈ r₁, BlindTo A label (space C₂ r₂) f) ∧ (∀ g ∈ r₂, BlindTo A label (space C₁ r₁) g) ∧
        ∀ u v, u <+: r₁ → v <+: r₂ → Separable A (follow label C₁ u) (follow label C₂ v) := by
  constructor
  · intro separated
    refine ⟨separated.left, separated.right, separated.leftBlind, separated.rightBlind, ?_⟩
    intro u v pu pv
    refine ⟨Finset.disjoint_of_subset_left
      ((follow_present_subset_space label C₁ u).trans (space_mono_prefix pu))
      (Finset.disjoint_of_subset_right
        ((follow_present_subset_space label C₂ v).trans (space_mono_prefix pv)) separated.apart), ?_⟩
    obtain ⟨σ, solved⟩ := separated.joint
    obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
    refine ⟨σ, ?_⟩
    rw [A.models_append, follow_equations, follow_equations, A.models_append, A.models_append]
    exact ⟨⟨one, models_prefix_added A label pu three⟩, ⟨two, models_prefix_added A label pv four⟩⟩
  · rintro ⟨left, right, leftBlind, rightBlind, stages⟩
    refine ⟨left, right, ?_, leftBlind, rightBlind, ?_⟩
    · refine Finset.disjoint_left.mpr fun o in₁ in₂ => ?_
      obtain ⟨u, pu, inU⟩ := (mem_space_iff_stage label C₁ r₁ o).mp in₁
      obtain ⟨v, pv, inV⟩ := (mem_space_iff_stage label C₂ r₂ o).mp in₂
      exact Finset.disjoint_left.mp (stages u v pu pv).1 inU inV
    · exact (SubstitutionAction.equivalent_consistent A
        (jointStore_equivalent A label C₁ r₁ C₂ r₂)).mpr
        (stages r₁ r₂ (List.prefix_refl _) (List.prefix_refl _)).2

/-- **`tensor_defined_iff` is separability of the ends.** For runs with disjoint spaces that are
blind to each other, the tensor run is defined exactly when the configurations they leave are
separable. -/
theorem tensor_defined_iff_separable_ends {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (left : Executable A label C₁ r₁) (right : Executable A label C₂ r₂)
    (apart : Disjoint (space C₁ r₁) (space C₂ r₂))
    (leftBlind : ∀ f ∈ r₁, BlindTo A label (space C₂ r₂) f)
    (rightBlind : ∀ g ∈ r₂, BlindTo A label (space C₁ r₁) g) :
    Executable A label (tensor C₁ C₂) (r₁ ++ r₂) ↔
      Separable A (follow label C₁ r₁) (follow label C₂ r₂) := by
  rw [tensor_defined_iff A label left right apart leftBlind rightBlind]
  have same := SubstitutionAction.equivalent_consistent A (jointStore_equivalent A label C₁ r₁ C₂ r₂)
  constructor
  · intro joint
    exact ⟨Finset.disjoint_of_subset_left (follow_present_subset_space label C₁ r₁)
      (Finset.disjoint_of_subset_right (follow_present_subset_space label C₂ r₂) apart),
      same.mp joint⟩
  · intro sep
    exact same.mpr sep.2

/-- **For empty runs, the definedness of the tensor is separability.** -/
theorem tensor_nil_iff_separable {C₁ C₂ : Configuration T O} (live₁ : A.Consistent C₁.equations)
    (live₂ : A.Consistent C₂.equations) (apart : Disjoint C₁.present C₂.present) :
    Executable A label (tensor C₁ C₂) ([] ++ []) ↔ Separable A C₁ C₂ := by
  have spaces : Disjoint (space C₁ ([] : List (Firing T S O))) (space C₂ ([] : List (Firing T S O))) := by
    simpa [space, madeBy] using apart
  exact tensor_defined_iff_separable_ends A label live₁ live₂ spaces
    (fun f member => by cases member) (fun g member => by cases member)

/-- A separated pair of runs leaves separable configurations. -/
theorem Separated.ends_separable {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) :
    Separable A (follow label C₁ r₁) (follow label C₂ r₂) :=
  ((separated_iff_stages A label).mp separated).2.2.2.2 r₁ r₂ (List.prefix_refl _)
    (List.prefix_refl _)

/-- A separated pair of runs starts from separable configurations. -/
theorem Separated.starts_separable {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) : Separable A C₁ C₂ :=
  ((separated_iff_stages A label).mp separated).2.2.2.2 [] [] List.nil_prefix List.nil_prefix

end Stages

/-! ## Unique splitting -/

section Splitting

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **An anchored firing** takes or reads an occurrence. -/
def Anchored (f : Firing T S O) : Prop := f.selection.taken ≠ [] ∨ f.selection.read ≠ []

/-- An admitted anchored firing uses an occurrence of the configuration it fires at. -/
theorem Anchored.uses {f : Firing T S O} {C : Configuration T O} (anchored : Anchored f)
    (valid : f.Valid A label C) :
    ∃ o ∈ C.present, o ∈ f.selection.taken ∨ o ∈ f.selection.read := by
  rcases anchored with taken | read
  · obtain ⟨o, member⟩ := List.exists_mem_of_ne_nil _ taken
    exact ⟨o, valid.firing.occurrences.taken_subset (by simpa [Selection.commit] using member),
      Or.inl member⟩
  · obtain ⟨o, member⟩ := List.exists_mem_of_ne_nil _ read
    exact ⟨o, valid.firing.occurrences.kept_subset (by simpa [Selection.commit] using member),
      Or.inr member⟩

/-- An occurrence an admitted firing uses is present where it fires. -/
theorem used_present {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C) {o : O}
    (used : o ∈ f.selection.taken ∨ o ∈ f.selection.read) : o ∈ C.present := by
  rcases used with taken | read
  · exact valid.firing.occurrences.taken_subset (by simpa [Selection.commit] using taken)
  · exact valid.firing.occurrences.kept_subset (by simpa [Selection.commit] using read)

/-- One side of the splitting argument: the second half of one split cannot begin inside the first
half of another. -/
theorem split_side {C₁ C₂ : Configuration T O} {r₁ r₂' m : List (Firing T S O)} {g : Firing T S O}
    (sep₁ : Separated A label C₁ (r₁ ++ g :: m) C₂ r₂')
    (headValid : g.Valid A label C₂) (anchored : Anchored g) : False := by
  obtain ⟨o, present, used⟩ := anchored.uses A label headValid
  have later := executable_append_right A label C₁ r₁ (g :: m) sep₁.left
  have inMiddle : o ∈ (follow label C₁ r₁).present := used_present A label later.1 used
  have inSpace₁ : o ∈ space C₁ (r₁ ++ g :: m) :=
    space_mono_prefix (List.prefix_append r₁ (g :: m))
      (follow_present_subset_space label C₁ r₁ inMiddle)
  exact Finset.disjoint_left.mp sep₁.apart inSpace₁ (Finset.mem_union_left _ present)

/-- **Unique splitting.** When every firing of the second halves is anchored, a word splits into
two separated runs from given halves in only one way. -/
theorem tensor_split_unique {C₁ C₂ : Configuration T O} {r₁ r₂ r₁' r₂' : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) (separated' : Separated A label C₁ r₁' C₂ r₂')
    (anchored : ∀ g ∈ r₂, Anchored g) (anchored' : ∀ g ∈ r₂', Anchored g)
    (same : r₁ ++ r₂ = r₁' ++ r₂') : r₁ = r₁' ∧ r₂ = r₂' := by
  rcases List.append_eq_append_iff.mp same with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · cases a' with
    | nil => exact ⟨by simpa using h₁.symm, by simpa using h₂⟩
    | cons g m =>
        subst h₁
        subst h₂
        exact (split_side A label separated' separated.right.1
          (anchored g List.mem_cons_self)).elim
  · cases c' with
    | nil => exact ⟨by simpa using h₁, by simpa using h₂.symm⟩
    | cons g m =>
        subst h₁
        subst h₂
        exact (split_side A label separated separated'.right.1
          (anchored' g List.mem_cons_self)).elim

end Splitting

end SeparationRuns

open SeparationRuns

#print axioms consistent_append_comm
#print axioms separable_comm
#print axioms separable_assoc
#print axioms separable_unit_right
#print axioms separable_unit_left
#print axioms tensor_congr
#print axioms separable_congr
#print axioms decompose_sameUpTo
#print axioms decompose_separable
#print axioms separable_self_iff
#print axioms knowledge_duplicable
#print axioms not_separable_of_mem
#print axioms present_cancel
#print axioms tensor_cancel
#print axioms tensor_sameUpTo_cancel_iff
#print axioms joinClass_functional
#print axioms joinClass_comm
#print axioms joinClass_assoc
#print axioms joinClass_unit_iff
#print axioms joinClass_knowledge_self
#print axioms follow_present_subset_space
#print axioms space_mono_prefix
#print axioms mem_space_iff_stage
#print axioms jointStore_equivalent
#print axioms separated_iff_stages
#print axioms tensor_defined_iff_separable_ends
#print axioms tensor_nil_iff_separable
#print axioms Separated.ends_separable
#print axioms Separated.starts_separable
#print axioms Anchored.uses
#print axioms split_side
#print axioms tensor_split_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
