import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullSeparations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StoreComposition
import Mettapedia.OSLF.Syntax.RhoScopedParallelEvents

/-!
# Absence is not compositional

An absence claim has the whole store as its scope. Putting another store beside it can falsify the
claim, so admission of an absence-guarded firing is not monotone under the union of stores, while
admission of firings that only take, read, make and tell is, as long as the knowledge of the union
stays solvable.

## On the first-order step

Two configurations side by side (`unionOf`) hold the union of the stores and both knowledges.

* `valid_unionOf`, for every substitution action: a firing admitted at `C` is admitted beside `D`
  when its made identities are new to `D`, its equations at `C` have a solution that also solves
  `D`'s knowledge, and its checks hold on the union.
* `positive_admission_monotone`, for every substitution action: **take, read, make and tell admission
  is monotone** under the union, equality checks included, given that joint solution. The hypothesis
  is needed beyond ground terms: `Controls.makeX_refused_beside` puts the knowledge `X = false`
  beside `X = true`; each is solvable, their union is not, and a firing that only makes is refused
  there. `Controls.makeX_kept_beside` is a positive instance over terms with variables.
  `positive_admission_iff`: given the rest, admission beside `D` holds exactly when that joint
  solution exists.
* On ground terms (`base`, `union`) a knowledge is solvable exactly when its equations have identical
  sides; `valid_union` and `positive_monotone` are the ground instances.
* `absent_union_iff`: an absence claim holds on a union exactly when it holds on each part.
* `guarded_union_iff`, on ground terms: **the grade of absence**: an absence-guarded firing admitted
  at `C` stays admitted beside `D` exactly when `D` has no occurrence of the pattern.
* `absence_not_monotone`: `spawn` (make `T` where `U` is absent) is admitted at the empty store and
  refused beside the store holding `U`.

This is the step's form of the boundary of the knowledge-tensor reading of runs
(`absence_has_no_additive_tensor_reading`): absence has no additive reading, because the frame rule
holds for it only on its grade.

## Stores, terms and rho

* `storeStep_frameClosed`: every store step of a reaction is closed under adding a frame;
  `absentStep_not_frameClosed`, `no_reaction_is_absence`: the absence step is not, so no reaction
  presents it.
* `reduces_parClosed`: reduction modulo the structural congruence is closed under parallel
  composition; `absentReduces_not_parClosed`, `parClosed_not_absence`: so no such relation is the
  absence step read through heating.
* `rho_step_not_join_sensitive`: the reduction of every rho rule set is closed under parallel
  composition (`RhoScopedParallelEvents.step_join`), so no relation that a parallel component can
  switch off is the reduction of a rho rule set.
* `AbsenceStep c a`: **the absence step on rho processes**, make `a` where `c` is not a parallel
  component, modulo rho's structural congruence. `rho_step_not_absence`: when the canonical form of
  `c` is not null, this step is not the reduction of any rho rule set; `rho_step_not_absence_of_output`
  is the instance for the output process, and `absenceStep_examples` shows the step firing and
  refused. `zero_absence_is_empty_reduction`: for the null process the absence step is empty, as is
  the reduction of a rule set that admits no rule, so the hypothesis on `c` is needed.

These theorems compare relations on the same processes. Encodings are not addressed: a process that
owns a store and answers absence queries about it, or a translation into other processes, is outside
them. Absence is meaningful on owned stores read as a whole, which is what the step's guard reads
(`absence_admits`, `guarded_union_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition

open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled)

/-! ## On the first-order step -/

section Every

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]

/-- **Two configurations side by side**, over any terms, solutions and occurrences: the union of the
stores and both knowledges. On ground terms it is `union`. -/
def unionOf (C D : Configuration T O) : Configuration T O :=
  ⟨C.equations ++ D.equations, C.present ∪ D.present⟩

/-- A solution of a firing's equations beside `D` is a solution of its equations at `C` that also
solves `D`'s knowledge. -/
theorem models_problem_unionOf (A : SubstitutionAction T S) (label : O → T)
    (f : AnnotatedRuns.Firing T S O) (C D : Configuration T O) (σ : S) :
    A.Models σ (f.selection.problem label f.rule (unionOf C D)) ↔
      A.Models σ (f.selection.problem label f.rule C) ∧ A.Models σ D.equations := by
  simp only [Selection.problem, unionOf, SubstitutionAction.models_append]
  tauto

/-- **A valid firing stays valid beside another store**, for every substitution action: when its
made identities are new to `D`, its equations at `C` have a solution that also solves `D`'s
knowledge, and its checks hold on the union. -/
theorem valid_unionOf {A : SubstitutionAction T S} {label : O → T} {C D : Configuration T O}
    {f : AnnotatedRuns.Firing T S O} (valid : f.Valid A label C)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present)
    (joint : ∃ σ, A.Models σ (f.selection.problem label f.rule C) ∧ A.Models σ D.equations)
    (checks : ∀ c ∈ f.rule.checks, A.Entails (f.selection.problem label f.rule (unionOf C D))
      (fun σ => c.Holds A σ label (unionOf C D).present))
    (noQueries : f.queries = []) : f.Valid A label (unionOf C D) := by
  have firing := valid.firing
  obtain ⟨takenSub, keptSub, apart, fresh, _⟩ := firing.occurrences
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ⟨fun o member => Finset.mem_union_left _ (takenSub member),
      fun o member => Finset.mem_union_left _ (keptSub member), apart, ?_, ?_⟩, ?_, checks⟩, ?_⟩
  · show Disjoint _ (C.present ∪ D.present)
    rw [Finset.disjoint_union_right]
    refine ⟨fresh, Finset.disjoint_left.mpr fun {o} made inD => freshInD o ?_ inD⟩
    exact List.mem_toFinset.mp made
  · intro query member
    simp [Selection.commit] at member
  · obtain ⟨σ, onC, onD⟩ := joint
    exact ⟨σ, (models_problem_unionOf A label f C D σ).mpr ⟨onC, onD⟩⟩
  · intro query member
    rw [noQueries] at member
    exact absurd member List.not_mem_nil

/-- **Take, read, make and tell admission is monotone under the union of stores**, for every
substitution action. A firing whose checks are equalities and which asks no query, admitted at `C`,
stays admitted beside `D` when its made identities are new to `D` and its equations at `C` have a
solution that also solves `D`'s knowledge. Beyond ground terms that joint solution is needed
(`Controls.makeX_refused_beside`). -/
theorem positive_admission_monotone {A : SubstitutionAction T S} {label : O → T}
    {C D : Configuration T O} {f : AnnotatedRuns.Firing T S O}
    (equalities : ∀ c ∈ f.rule.checks, ∃ l r, c = Check.equal l r) (noQueries : f.queries = [])
    (admitted : (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present)
    (joint : ∃ σ, A.Models σ (f.selection.problem label f.rule C) ∧ A.Models σ D.equations) :
    (AnnotatedRuns.firstOrder A label).toStep.Admits (s := unionOf C D) f := by
  have valid : f.Valid A label C := admitted
  refine valid_unionOf valid freshInD joint ?_ noQueries
  intro c member σ solved
  obtain ⟨l, r, rfl⟩ := equalities c member
  exact valid.firing.checks _ member σ ((models_problem_unionOf A label f C D σ).mp solved).1

/-- **The joint solution is exactly what admission beside `D` needs.** For a firing whose checks are
equalities and which asks no query, admitted at `C`, with made identities new to `D`: it is admitted
beside `D` exactly when its equations at `C` have a solution that also solves `D`'s knowledge. -/
theorem positive_admission_iff {A : SubstitutionAction T S} {label : O → T}
    {C D : Configuration T O} {f : AnnotatedRuns.Firing T S O}
    (equalities : ∀ c ∈ f.rule.checks, ∃ l r, c = Check.equal l r) (noQueries : f.queries = [])
    (admitted : (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) :
    (AnnotatedRuns.firstOrder A label).toStep.Admits (s := unionOf C D) f ↔
      ∃ σ, A.Models σ (f.selection.problem label f.rule C) ∧ A.Models σ D.equations := by
  constructor
  · intro beside
    obtain ⟨σ, solved⟩ := (show f.Valid A label (unionOf C D) from beside).firing.consistent
    exact ⟨σ, (models_problem_unionOf A label f C D σ).mp solved⟩
  · exact positive_admission_monotone equalities noQueries admitted freshInD

end Every

/-- Two configurations side by side, on ground terms: `unionOf` at `Conf`. -/
def union (C D : Conf) : Conf := ⟨C.equations ++ D.equations, C.present ∪ D.present⟩

theorem union_eq_unionOf (C D : Conf) : union C D = unionOf C D := rfl

/-- **On ground terms, a valid firing stays valid beside another store** whose occurrences its made
identities avoid, whose knowledge has the identity solution, and where its checks hold on the
union. -/
theorem valid_union {C D : Conf} {f : Fir} (valid : f.Valid ground Prod.fst C)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present)
    (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2)
    (checks : ∀ c ∈ f.rule.checks, c.Holds ground () Prod.fst (union C D).present)
    (noQueries : f.queries = []) : f.Valid ground Prod.fst (union C D) := by
  have firing := valid.firing
  obtain ⟨takenSub, keptSub, apart, fresh, _⟩ := firing.occurrences
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ⟨fun o member => Finset.mem_union_left _ (takenSub member),
      fun o member => Finset.mem_union_left _ (keptSub member), apart, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · show Disjoint _ (C.present ∪ D.present)
    rw [Finset.disjoint_union_right]
    refine ⟨fresh, Finset.disjoint_left.mpr fun {o} made inD => freshInD o ?_ inD⟩
    exact List.mem_toFinset.mp made
  · intro query member
    simp [Selection.commit] at member
  · obtain ⟨u, solved⟩ := firing.consistent
    refine ⟨u, fun e member => ?_⟩
    simp only [Selection.problem, union, List.mem_append] at member
    rcases member with (((old | added) | taken) | read) | told
    · exact solved e (by simp [Selection.problem, old])
    · exact knowledgeD e added
    · exact solved e (by simp [Selection.problem, taken])
    · exact solved e (by simp [Selection.problem, read])
    · exact solved e (by simp [Selection.problem, told])
  · intro check member u _
    exact checks check member
  · intro query member
    rw [noQueries] at member
    exact absurd member List.not_mem_nil

/-- **The ground instance of `positive_admission_monotone`.** On ground terms a knowledge is solvable
exactly when its equations have identical sides, so take, read, make and tell admission survives the
union with a store whose knowledge has identical sides and whose occurrences the made identities
avoid. -/
theorem positive_monotone {C D : Conf} {f : Fir} (noChecks : f.rule.checks = [])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := union C D) f := by
  obtain ⟨u, solved⟩ := (show f.Valid ground Prod.fst C from admitted).firing.consistent
  exact positive_admission_monotone
    (by rw [noChecks]; exact fun c member => absurd member List.not_mem_nil)
    noQueries admitted freshInD ⟨u, solved, knowledgeD⟩

/-- **An absence claim holds on a union exactly when it holds on each part.** -/
theorem absent_union_iff {C D : Conf} {p : Expr} :
    (Check.absent p).Holds ground () Prod.fst (union C D).present ↔
      (Check.absent p).Holds ground () Prod.fst C.present ∧
        (Check.absent p).Holds ground () Prod.fst D.present := by
  constructor
  · intro onUnion
    exact ⟨fun o member => onUnion o (Finset.mem_union_left _ member),
      fun o member => onUnion o (Finset.mem_union_right _ member)⟩
  · rintro ⟨onC, onD⟩ o member
    rcases Finset.mem_union.mp member with inC | inD
    · exact onC o inC
    · exact onD o inD

/-- The absence check of an admitted guarded firing holds where it fires. -/
theorem guard_holds {C : Conf} {f : Fir} {p : Expr} (guard : f.rule.checks = [.absent p])
    (valid : f.Valid ground Prod.fst C) : (Check.absent p).Holds ground () Prod.fst C.present := by
  obtain ⟨u, solved⟩ := valid.firing.consistent
  exact valid.firing.checks _ (by rw [guard]; exact List.mem_singleton_self _) u solved

/-- **The grade of absence, on ground terms**: an absence-guarded firing admitted at `C` stays
admitted beside `D` exactly when `D` has no occurrence of the pattern. -/
theorem guarded_union_iff {C D : Conf} {f : Fir} {p : Expr} (guard : f.rule.checks = [.absent p])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := union C D) f ↔ (Check.absent p).Holds ground () Prod.fst D.present := by
  constructor
  · intro onUnion
    exact (absent_union_iff.mp (guard_holds guard onUnion)).2
  · intro onD
    refine valid_union admitted freshInD knowledgeD ?_ noQueries
    rw [guard]
    intro c member
    rw [List.mem_singleton.mp member]
    exact absent_union_iff.mpr ⟨guard_holds guard admitted, onD⟩

/-- **Absence is not monotone**: `spawn` is admitted at the empty store and refused beside the store
holding `U`. -/
theorem absence_not_monotone :
    ∃ (C D : Conf) (f : Fir), base.Admits (s := C) f ∧ ¬ base.Admits (s := union C D) f := by
  refine ⟨Separations.emptyS.1, Separations.onlyU.1, Separations.spawnAt.1,
    Separations.spawn_admitted.1, fun onUnion => ?_⟩
  have clear := (guarded_union_iff (D := Separations.onlyU.1) (f := Separations.spawnAt.1) rfl rfl
    Separations.spawn_admitted.1 (by decide) (by decide)).mp onUnion
  exact clear (factU, 0) (by decide) rfl

/-! ## Beyond ground terms the union's knowledge must stay solvable -/

namespace Controls

open Mettapedia.Logic.LP
open Rational.Controls (ctlSig X labelX)

/-- Knowledge binding `X` to `true`, nothing present. -/
def bindTrue : Configuration (Term ctlSig) ℕ := ⟨[(X, .const true)], ∅⟩

/-- Knowledge binding `X` to `false`, nothing present. -/
def bindFalse : Configuration (Term ctlSig) ℕ := ⟨[(X, .const false)], ∅⟩

/-- Knowledge binding `X` to `true`, beside the occurrence `7`. -/
def bindTrueAt7 : Configuration (Term ctlSig) ℕ := ⟨[(X, .const true)], {7}⟩

/-- Make the occurrence `0`, labelled `X`; take, read, tell and check nothing. -/
def makeX : AnnotatedRuns.Firing (Term ctlSig) (Subst ctlSig) ℕ :=
  ⟨⟨[], [], [], [], [X]⟩, [], ⟨[], [], [0]⟩⟩

/-- The first-order step over terms with variables, every occurrence labelled `X`. -/
abbrev termStep := (AnnotatedRuns.firstOrder (FirstOrder.action ctlSig) labelX).toStep

/-- Every variable to `true`. -/
def allTrue : Subst ctlSig := fun _ => .const true

theorem allTrue_models : (FirstOrder.action ctlSig).Models allTrue [(X, .const true)] := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

/-- Each knowledge alone is solvable. -/
theorem bindFalse_consistent : (FirstOrder.action ctlSig).Consistent bindFalse.equations := by
  refine ⟨fun _ => .const false, fun e member => ?_⟩
  rw [List.mem_singleton.mp member]
  rfl

/-- `makeX` is admitted at `bindTrue`. -/
theorem makeX_admitted : termStep.Admits (s := bindTrue) makeX := by
  show PredicateQueryAdmission.Valid (FirstOrder.action ctlSig) labelX makeX.rule [] bindTrue
    makeX.selection
  refine (PredicateQueryAdmission.valid_empty_iff (FirstOrder.action ctlSig) labelX makeX.rule bindTrue
    makeX.selection).mpr ⟨List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, ?_,
      ⟨allTrue, allTrue_models⟩, fun c member => absurd member List.not_mem_nil⟩
  exact ⟨by simp [Selection.commit, makeX], by simp [Selection.commit, makeX],
    by simp [Selection.commit, makeX], by simp [Selection.commit, makeX, bindTrue],
    by simp [Selection.commit]⟩

/-- **Control: joint solvability is needed.** `X = false` beside `X = true`: each knowledge is
solvable (`allTrue_models`, `bindFalse_consistent`), their union is not, and the firing that only
makes, admitted at `bindTrue`, is refused beside `bindFalse`. -/
theorem makeX_refused_beside : ¬ termStep.Admits (s := unionOf bindTrue bindFalse) makeX := by
  intro admitted
  have valid : makeX.Valid (FirstOrder.action ctlSig) labelX (unionOf bindTrue bindFalse) := admitted
  obtain ⟨θ, solved⟩ := valid.firing.consistent
  have isTrue : θ 0 = .const true :=
    solved (X, .const true) (by simp [Selection.problem, unionOf, bindTrue])
  have isFalse : θ 0 = .const false :=
    solved (X, .const false) (by simp [Selection.problem, unionOf, bindFalse])
  have clash := isTrue.symm.trans isFalse
  simp at clash

/-- **Positive instance over terms with variables.** Beside a store whose knowledge the same
solution solves, the firing that only makes stays admitted (`positive_admission_monotone`). -/
theorem makeX_kept_beside : termStep.Admits (s := unionOf bindTrue bindTrueAt7) makeX :=
  positive_admission_monotone (fun _ member => absurd member List.not_mem_nil) rfl makeX_admitted
    (by decide) ⟨allTrue, allTrue_models, allTrue_models⟩

end Controls

/-! ## Stores, terms and rho -/

section Stores

variable {A : Type*}

open StoreComposition

/-- A relation on stores closed under adding a frame. -/
def FrameClosed (R : Multiset A → Multiset A → Prop) : Prop :=
  ∀ before after frame, R before after → R (before + frame) (after + frame)

/-- **Every store step of a reaction is closed under adding a frame.** -/
theorem storeStep_frameClosed (react : Reaction A) : FrameClosed (StoreStep react) := by
  rintro before after frame ⟨consumed, produced, rest, reacts, rfl, rfl⟩
  exact ⟨consumed, produced, rest + frame, reacts, Multiset.add_assoc _ _ _,
    Multiset.add_assoc _ _ _⟩

/-- The absence step: make `a` where `c` is absent. -/
def AbsentStep (c a : A) (before after : Multiset A) : Prop := c ∉ before ∧ after = before + {a}

theorem absentStep_not_frameClosed (c a : A) : ¬ FrameClosed (AbsentStep c a) := by
  intro closed
  have here : AbsentStep c a 0 {a} := ⟨Multiset.notMem_zero c, (Multiset.zero_add _).symm⟩
  exact (closed 0 {a} {c} here).1 (by simp)

/-- **No reaction presents the absence step.** -/
theorem no_reaction_is_absence (c a : A) (react : Reaction A) :
    ¬ ∀ before after, StoreStep react before after ↔ AbsentStep c a before after := by
  intro same
  apply absentStep_not_frameClosed c a
  intro before after frame step
  exact (same _ _).mp (storeStep_frameClosed react before after frame ((same _ _).mpr step))

/-- A relation on terms closed under parallel composition. -/
def ParClosed (R : Term A → Term A → Prop) : Prop :=
  ∀ t t' u, R t t' → R (Term.join t u) (Term.join t' u)

/-- **Reduction modulo the congruence is closed under parallel composition.** -/
theorem reduces_parClosed (react : Reaction A) : ParClosed (Reduces react) := by
  rintro t t' u ⟨s, s', first, inner, last⟩
  exact ⟨Term.join s u, Term.join s' u,
    Term.Congruent.join_congr first (Term.Congruent.refl u), LocalStep.left u inner,
    Term.Congruent.join_congr last (Term.Congruent.refl u)⟩

/-- The absence step read on terms through heating. -/
def AbsentReduces (c a : A) (t t' : Term A) : Prop := AbsentStep c a (Term.heat t) (Term.heat t')

theorem absentReduces_not_parClosed (c a : A) : ¬ ParClosed (AbsentReduces c a) := by
  intro closed
  have here : AbsentReduces c a Term.unit (Term.atom a) := ⟨by simp, by simp⟩
  exact (closed _ _ (Term.atom c) here).1 (by simp)

/-- **No relation closed under parallel composition is the absence step.** -/
theorem parClosed_not_absence {R : Term A → Term A → Prop} (closed : ParClosed R) (c a : A) :
    ¬ ∀ t t', R t t' ↔ AbsentReduces c a t t' := by
  intro same
  apply absentReduces_not_parClosed c a
  intro t t' u step
  exact (same _ _).mp (closed t t' u ((same _ _).mpr step))

end Stores

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

variable {Index : Type*} {rules : Index → RhoScopedParallelEvents.ProcessRule} {admitted : Index → Prop}
  {context : Ctx sig}

/-- **No relation that a parallel component switches off is the reduction of a rho rule set.** The
reduction of every rho rule set is closed under parallel composition (`step_join`); a relation that
relates `first` to `second` and stops relating them once `extra` is put beside both is not. -/
theorem rho_step_not_join_sensitive {R : Process context → Process context → Prop}
    {first second extra : Process context} (holds : R first second)
    (switchedOff : ¬ R (join first extra) (join second extra)) :
    ¬ ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) x y ↔ R x y := by
  intro same
  exact switchedOff ((same _ _).mp (RhoScopedParallelEvents.step_join ((same _ _).mpr holds) extra))

/-! ### The absence step on rho processes -/

/-- `c` is a parallel component of `P`, modulo rho's structural congruence. -/
def Component (c P : Process context) : Prop := ∃ rest, P = join c rest

/-- **The absence step on rho processes**: make `a` where `c` is not a parallel component. -/
def AbsenceStep (c a P Q : Process context) : Prop := ¬ Component c P ∧ Q = join P a

theorem component_join (c P : Process context) : Component c (join P c) :=
  ⟨P, join_commutes P c⟩

/-- **A parallel `c` switches the absence step off.** -/
theorem absenceStep_switched_off (c a P Q : Process context) :
    ¬ AbsenceStep c a (join P c) (join Q c) :=
  fun step => step.1 (component_join c P)

section Canonical

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize collapseBag
  normalizeBagElements bagContents sortPatterns IsCanonical IsCanonicalList isCanonicalList_of_forall
  bagContents_collapse_normalized bagContents_zero_cons sortPatterns_perm
  normalizeBagElements_eq_sort_bagContents bagContents_append collapse_normalize_singleton_of_isCanonical
  canonicalize_isCanonical canonicalize_apply_general)

/-- A parallel pair whose first part is canonical and not null is not null once normalized. -/
theorem collapse_pair_ne_null {x y : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} (cx : IsCanonical x)
    (cy : IsCanonical y) (nonnull : x ≠ .apply "PZero" []) :
    collapseBag (normalizeBagElements [x, y]) ≠ .apply "PZero" [] := by
  intro same
  have pair : IsCanonicalList [x, y] := isCanonicalList_of_forall fun p member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact cx
    · rw [List.mem_singleton.mp member]
      exact cy
  have contents := bagContents_collapse_normalized pair
  rw [same, bagContents_zero_cons] at contents
  have emptyPair : normalizeBagElements [x, y] = [] := contents.symm.trans rfl
  have emptyContents : bagContents [x, y] = [] := by
    have perm := sortPatterns_perm (bagContents [x, y])
    rw [← normalizeBagElements_eq_sort_bagContents, emptyPair] at perm
    exact perm.eq_nil
  have emptyX : bagContents [x] = [] := by
    have split : bagContents [x, y] = bagContents [x] ++ bagContents [y] := bagContents_append [x] [y]
    rw [emptyContents] at split
    exact (List.append_eq_nil_iff.mp split.symm).1
  have collapsed := collapse_normalize_singleton_of_isCanonical cx
  rw [normalizeBagElements_eq_sort_bagContents, emptyX,
    show sortPatterns ([] : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) = [] from
      (sortPatterns_perm []).nil_eq.symm] at collapsed
  exact nonnull collapsed.symm

/-- The canonical form of the null process is null. -/
theorem encode_zero :
    IntrinsicEncoding.encodeEquationClass (RhoQuotationClassFibres.zero context) = .apply "PZero" [] := by
  show canonicalize (IntrinsicEncoding.encodeTerm (RhoEquationConstructorControls.null (Γ := context))) = _
  have nullCode : IntrinsicEncoding.encodeTerm (RhoEquationConstructorControls.null (Γ := context)) =
      .apply "PZero" [] := rfl
  rw [nullCode, canonicalize_apply_general "PZero" [] (by simp)]
  all_goals rfl

/-- **Beside a process whose canonical form is not null, nothing is null.** -/
theorem encode_join_ne_null (c rest : Process context)
    (nonnull : IntrinsicEncoding.encodeEquationClass c ≠ .apply "PZero" []) :
    IntrinsicEncoding.encodeEquationClass (join c rest) ≠ .apply "PZero" [] := by
  induction c using Quotient.inductionOn with
  | _ c =>
    induction rest using Quotient.inductionOn with
    | _ rest =>
      have parallelCode :
          IntrinsicEncoding.encodeTerm (RhoEquationConstructorControls.parallel c rest) =
            .collection .hashBag [IntrinsicEncoding.encodeTerm c, IntrinsicEncoding.encodeTerm rest]
              none := rfl
      show canonicalize (IntrinsicEncoding.encodeTerm
        (RhoEquationConstructorControls.parallel c rest)) ≠ _
      rw [parallelCode]
      change collapseBag (normalizeBagElements [canonicalize (IntrinsicEncoding.encodeTerm c),
        canonicalize (IntrinsicEncoding.encodeTerm rest)]) ≠ _
      exact collapse_pair_ne_null (canonicalize_isCanonical _) (canonicalize_isCanonical _) nonnull

/-- **The null process has no component whose canonical form is not null.** -/
theorem not_component_zero (c : Process context)
    (nonnull : IntrinsicEncoding.encodeEquationClass c ≠ .apply "PZero" []) :
    ¬ Component c (RhoQuotationClassFibres.zero context) := by
  rintro ⟨rest, same⟩
  apply encode_join_ne_null c rest nonnull
  rw [← same]
  exact encode_zero

/-- The output process `visible` has a canonical form that is not null. -/
theorem visible_nonnull : IntrinsicEncoding.encodeEquationClass visible ≠ .apply "PZero" [] := by
  show canonicalize (IntrinsicEncoding.encodeTerm RhoSourceOutputPredicate.output) ≠ _
  decide +kernel

end Canonical

/-- **The absence step is not a rho reduction.** For every `c` whose canonical form is not null and
every `a`, the absence step of `c` and `a` is not the reduction of any rho rule set: it relates the
null process to `a`, and a parallel `c` switches it off, while rho's reduction is closed under
parallel composition. Encodings of absence are not addressed. -/
theorem rho_step_not_absence (c a : Process context)
    (nonnull : IntrinsicEncoding.encodeEquationClass c ≠ .apply "PZero" []) :
    ¬ ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) x y ↔
      AbsenceStep c a x y :=
  rho_step_not_join_sensitive (R := AbsenceStep c a) (first := RhoQuotationClassFibres.zero context)
    (second := join (RhoQuotationClassFibres.zero context) a) (extra := c)
    ⟨not_component_zero c nonnull, rfl⟩ (absenceStep_switched_off c a _ _)

/-- **Instance**: for every rho rule set, the absence step of the output process is not its
reduction. -/
theorem rho_step_not_absence_of_output (a : Process []) :
    ¬ ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) x y ↔
      AbsenceStep visible a x y :=
  rho_step_not_absence visible a visible_nonnull

/-- **Examples.** The absence step of the output process fires at the null process, and never at the
output process itself. -/
theorem absenceStep_examples (a : Process []) :
    AbsenceStep visible a (RhoQuotationClassFibres.zero []) (join (RhoQuotationClassFibres.zero []) a) ∧
      ∀ Q, ¬ AbsenceStep visible a visible Q :=
  ⟨⟨not_component_zero visible visible_nonnull, rfl⟩,
    fun _ step => step.1 ⟨RhoQuotationClassFibres.zero [], (join_zero_right visible).symm⟩⟩

/-- **Control: the hypothesis on `c` is needed.** The null process is a component of every process,
so its absence step is empty, as is the reduction of a rule set that admits no rule: the two
coincide. -/
theorem zero_absence_is_empty_reduction (a : Process context) :
    ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := fun _ => False) x y ↔
      AbsenceStep (RhoQuotationClassFibres.zero context) a x y := by
  intro x y
  constructor
  · intro step
    obtain ⟨root, _, _, _⟩ := (RhoScopedParallelEvents.step_iff_root_surrounding x y).mp step
    exact False.elim root.1.2
  · rintro ⟨absent, _⟩
    exact (absent ⟨x, (join_zero_left x).symm⟩).elim

end Rho

#print axioms valid_unionOf
#print axioms positive_admission_monotone
#print axioms positive_admission_iff
#print axioms valid_union
#print axioms positive_monotone
#print axioms absent_union_iff
#print axioms guarded_union_iff
#print axioms absence_not_monotone
#print axioms Controls.makeX_refused_beside
#print axioms Controls.makeX_kept_beside
#print axioms no_reaction_is_absence
#print axioms parClosed_not_absence
#print axioms rho_step_not_join_sensitive
#print axioms rho_step_not_absence
#print axioms rho_step_not_absence_of_output
#print axioms absenceStep_examples
#print axioms zero_absence_is_empty_reduction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
