import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContractsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport

/-!
# Evidence reuse as reads with a region

The runtime typing draft reuses evidence proved at a call's entry, and invalidates it when a
declaration changes; its test is a generation counter that every declaration edit advances. Read as
firings, declarations are rows, membership is a guard read in the view of the present rows, and
reuse is sound exactly while no firing writes the guard's region (`Step.Guards`).

## Guards stay valid while their region is untouched (`guard_run`)

For any step with local guards: along a run none of whose firings writes the region of a guard, the
guard reads the same at the end as at the start. This holds for every instance of `Step.Guards`.

## Declarations as rows (`rowStep`)

* A row declares constructor rules per symbol and nominal facts (`Row`). The **declaration view** of a
  set of occurrences is the rows among them (`view`); membership is `DeclarationTyping.HasType` in
  that view.
* A **row firing** takes, reads and makes occurrences, tells equations, and checks memberships
  in the view of the present occurrences. Its guard is that check.
* **The fine region** of a membership `v ∈ τ` (`fineRegion`): the rows that declare a rule for a
  symbol of `v`, and the rows that declare facts. Membership reads nothing else (`member_inside`).
* **The coarse region** (`coarseRegion`): every declaration row. It is the generation counter's
  region: any declaration edit touches it.

Both are regions of guards for the row step (`fineGuards`, `coarseGuards`). Hence:

* **Evidence reuse is sound** (`reuse_sound`): a membership checked once holds at the end of every
  run that writes nothing in its fine region. Later firings may read the evidence instead of
  checking again.
* **The generation counter is sound** (`generation_sound`): a run that edits no declaration keeps every
  membership. It is coarse: the fine region lies inside it (`fine_subset_coarse`).

## Controls (`EvidenceControls`)

Row `0` declares numbers; rows `1` and `2` declare booleans. A membership `1 ∈ Number` is checked
and its evidence row made. Replacing row `1` by row `2` edits a declaration, so the generation counter
invalidates the evidence; the edit is outside the fine region, and the membership indeed survives
(`unrelated_edit`, `evidence_run_keeps_membership`). Retracting row `0` writes the fine region, and
the membership fails (`related_edit_breaks`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingEvidence

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Logic.ConstraintTypes renaming Tree → VTree
open Mettapedia.Logic.ConstraintTypes.SymbolicTypes (Closed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Interface (Frames)

/-! ## Guards along runs -/

section Runs

universe uO uT uH uOcc uS uF
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Interface.Step X O State Firing}

/-- **A guard stays valid along every run that writes nothing in its region.** -/
theorem guard_run [P.Guarded] (G : P.Guards) {s₀ : State} (f : Firing s₀) (b : Obj) (σ : Hom (P.target f) b) :
    ∀ {t : State} (r : P.Run t),
      (∀ x ∈ r.word, ∀ o ∈ G.region f b σ, ¬ Interface.Step.Writes (P.selection x.2) o) →
        (G.Guard f b σ (P.present r.last) ↔ G.Guard f b σ (P.present t))
  | _, .nil _, _ => Iff.rfl
  | _, .cons g admitted rest, outside => by
      have later := guard_run G f b σ rest fun x member => outside x (List.mem_cons_of_mem _ member)
      refine later.trans ?_
      rw [P.present_result]
      exact G.guard_fire f b σ _ _ (outside _ List.mem_cons_self)

end Runs

section Generic

/-! ## Declarations as rows -/

variable {U P Q C Sym : Type} {typeArity : C → Nat} {valueArity : Sym → Nat}

variable (U P Q C Sym typeArity valueArity) in
/-- What one declaration row declares. -/
structure Row where
  rules : (s : Sym) → List (ConstructorTyping.Rule P Q C typeArity (valueArity s))
  facts : List (DeclarationTyping.Fact U P Q C Sym typeArity valueArity)

variable {O : Type} [DecidableEq O]

/-- **The declaration view of present occurrences**: the declaration rows among them. -/
def view (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity) :
    DeclarationTyping.Declarations (Finset O) U P Q C Sym typeArity valueArity where
  childContext W _ _ := W
  constructors W s := (rows.filter (· ∈ W)).flatMap fun o => (row o).rules s
  facts W := (rows.filter (· ∈ W)).flatMap fun o => (row o).facts

/-- The symbols of a value. -/
def symbols : VTree Sym valueArity → List Sym
  | .node s children => s :: (List.finRange (valueArity s)).flatMap fun i => symbols (children i)

/-- **The fine region of a membership of `v`**: the rows declaring a rule for a symbol of `v`, and the
rows declaring facts. -/
def fineRegion (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity)
    (v : VTree Sym valueArity) : Set O :=
  {o | o ∈ rows ∧ ((∃ s ∈ symbols v, (row o).rules s ≠ []) ∨ (row o).facts ≠ [])}

/-- **The coarse region**: every declaration row. -/
def coarseRegion (rows : List O) : Set O := {o | o ∈ rows}

omit [DecidableEq O] in
theorem fine_subset_coarse (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity)
    (v : VTree Sym valueArity) : fineRegion rows row v ⊆ coarseRegion rows :=
  fun _ inside => inside.1

omit [DecidableEq O] in
theorem fineRegion_child (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity) (s : Sym)
    (children : Fin (valueArity s) → VTree Sym valueArity) (i : Fin (valueArity s)) :
    fineRegion rows row (children i) ⊆ fineRegion rows row (.node s children) := by
  rintro o ⟨present, (⟨s', occurs, declared⟩ | facts)⟩
  · refine ⟨present, .inl ⟨s', ?_, declared⟩⟩
    simp only [symbols, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
    exact .inr ⟨i, occurs⟩
  · exact ⟨present, .inr facts⟩

theorem member_transfer (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity)
    {W W' : Finset O} {v : VTree Sym valueArity} {τ : Closed Q C typeArity}
    (typed : DeclarationTyping.HasType (view rows row) W v τ)
    (same : ∀ o ∈ fineRegion rows row v, (o ∈ W ↔ o ∈ W')) :
    DeclarationTyping.HasType (view rows row) W' v τ := by
  induction typed with
  | @constructor Γ s children rule present parameters fields ih =>
      obtain ⟨o, kept, declared⟩ := List.mem_flatMap.mp present
      obtain ⟨listed, inW⟩ := List.mem_filter.mp kept
      have inside : o ∈ fineRegion rows row (.node s children) :=
        ⟨listed, .inl ⟨s, List.mem_cons_self, List.ne_nil_of_mem declared⟩⟩
      have inW' : o ∈ W' := (same o inside).mp (of_decide_eq_true inW)
      refine .constructor rule
        (List.mem_flatMap.mpr ⟨o, List.mem_filter.mpr ⟨listed, decide_eq_true inW'⟩, declared⟩)
        parameters ?_
      intro i fieldType required
      exact ih i fieldType required fun o' inside' =>
        same o' (fineRegion_child rows row s children i inside')
  | @nominal Γ v fact present values matched parameters bound =>
      obtain ⟨o, kept, declared⟩ := List.mem_flatMap.mp present
      obtain ⟨listed, inW⟩ := List.mem_filter.mp kept
      have inside : o ∈ fineRegion rows row v := ⟨listed, .inr (List.ne_nil_of_mem declared)⟩
      have inW' : o ∈ W' := (same o inside).mp (of_decide_eq_true inW)
      exact .nominal fact
        (List.mem_flatMap.mpr ⟨o, List.mem_filter.mpr ⟨listed, decide_eq_true inW'⟩, declared⟩)
        values matched parameters bound

/-- **Membership reads only its fine region.** -/
theorem member_inside (rows : List O) (row : O → Row U P Q C Sym typeArity valueArity)
    {W W' : Finset O} (v : VTree Sym valueArity) (τ : Closed Q C typeArity)
    (same : ∀ o ∈ fineRegion rows row v, (o ∈ W ↔ o ∈ W')) :
    DeclarationTyping.HasType (view rows row) W v τ ↔ DeclarationTyping.HasType (view rows row) W' v τ :=
  ⟨fun typed => member_transfer rows row typed same,
    fun typed => member_transfer rows row typed fun o inside => (same o inside).symm⟩

/-! ## The row step -/


/-- **A row firing**: a selection, tells, and memberships checked in the present view. -/
structure RowFiring (Q C Sym : Type) (typeArity : C → Nat) (valueArity : Sym → Nat) (O T : Type) where
  selection : Selection O
  tells : EquationStore T
  checks : List (VTree Sym valueArity × Closed Q C typeArity)

variable {T S : Type} (A : SubstitutionAction T S) (rows : List O)
  (row : O → Row U P Q C Sym typeArity valueArity)

/-- The guard of a row firing: its memberships, in the view of the occurrences `W`. -/
def Checked (f : RowFiring Q C Sym typeArity valueArity O T) (W : Finset O) : Prop :=
  ∀ c ∈ f.checks, DeclarationTyping.HasType (view rows row) W c.1 c.2

/-- **The row step**, over the one-frame category of `A`. -/
def rowStep :
    Interface.Step.Standard (Frames.ofSubstitution A) O (Configuration T O)
      (fun _ => RowFiring Q C Sym typeArity valueArity O T) where
  frame _ := PUnit.unit
  knowledge C := C.equations
  present C := C.present
  selection f := f.selection
  target _ := PUnit.unit
  extension _ := A.identity
  information {C} f := C.equations ++ f.tells
  transported := by
    intro C f e member
    show (A.apply A.identity e.1, A.apply A.identity e.2) ∈ C.equations ++ f.tells
    rw [A.apply_identity, A.apply_identity]
    exact List.mem_append_left _ member
  Shapes f := f.selection.taken.Nodup ∧ f.selection.made.Nodup
  Holds {C} f _ _ := Checked rows row f C.present
  Admits {C} f := (f.selection.taken.Nodup ∧ f.selection.made.Nodup) ∧
    Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
    (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (C.equations ++ f.tells) ∧
    (Frames.ofSubstitution A).Entails (a := PUnit.unit) (C.equations ++ f.tells)
      (fun _ _ => Checked rows row f C.present)
  admits_iff _ := Iff.rfl
  preparedResult {C} f _ := ⟨C.equations ++ f.tells, fire C.present (f.selection.commit (T := Unit))⟩
  present_preparedResult _ _ := rfl
  preparedSettle _ _ := A.identity
  knowledge_preparedResult {C} f _ :=
    (Frames.applyStore_id (X := Frames.ofSubstitution A) (C.equations ++ f.tells)).symm

/-- **The guards of the row step, with fine regions.** -/
def fineGuards : (rowStep A rows row).Guards where
  Guard f _ _ W := Checked rows row f W
  region f _ _ := {o | ∃ c ∈ f.checks, o ∈ fineRegion rows row c.1}
  holds_iff _ _ _ := Iff.rfl
  respects _ _ _ _ _ _ := Iff.rfl
  inside _ _ _ _ _ same := forall_congr' fun c => imp_congr_right fun member =>
    member_inside rows row c.1 c.2 fun o inside => same o ⟨c, member, inside⟩

/-- **The guards of the row step, with the generation counter's region**: every declaration row. -/
def coarseGuards : (rowStep A rows row).Guards where
  Guard f _ _ W := Checked rows row f W
  region _ _ _ := coarseRegion rows
  holds_iff _ _ _ := Iff.rfl
  respects _ _ _ _ _ _ := Iff.rfl
  inside _ _ _ _ _ same := forall_congr' fun c => imp_congr_right fun _ =>
    member_inside rows row c.1 c.2 fun o inside => same o (fine_subset_coarse rows row c.1 inside)

/-- **Evidence reuse is sound.** A membership a firing checked at `s₀` holds at the end of every run
that writes nothing in its fine region. -/
theorem reuse_sound {s₀ : Configuration T O} (f : RowFiring Q C Sym typeArity valueArity O T)
    (checked : Checked rows row f s₀.present) {t : Configuration T O} (r : (rowStep A rows row).Run t)
    (start : t.present = s₀.present)
    (outside : ∀ x ∈ r.word, ∀ o, (∃ c ∈ f.checks, o ∈ fineRegion rows row c.1) →
      ¬ Interface.Step.Writes x.2.selection o) :
    Checked rows row f r.last.present := by
  have law := guard_run (fineGuards A rows row) (s₀ := s₀) f PUnit.unit A.identity r outside
  exact law.mpr (show Checked rows row f t.present by rw [start]; exact checked)

/-- **The generation counter is sound**: a run that writes no declaration row keeps every
membership. -/
theorem generation_sound {s₀ : Configuration T O} (f : RowFiring Q C Sym typeArity valueArity O T)
    (checked : Checked rows row f s₀.present) {t : Configuration T O} (r : (rowStep A rows row).Run t)
    (start : t.present = s₀.present)
    (noEdit : ∀ x ∈ r.word, ∀ o ∈ rows, ¬ Interface.Step.Writes x.2.selection o) :
    Checked rows row f r.last.present := by
  have law := guard_run (coarseGuards A rows row) (s₀ := s₀) f PUnit.unit A.identity r
    fun x member o inside => noEdit x member o inside
  exact law.mpr (show Checked rows row f t.present by rw [start]; exact checked)

/-! ## Controls -/

end Generic

namespace EvidenceControls

open TypingContractsControls (Sym valueArity Name typeArity leaf)

/-- The trivial knowledge: one term, one substitution. -/
def trivial : SubstitutionAction PUnit PUnit where
  E := Eq
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := PUnit.unit
  compose _ _ := PUnit.unit
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

/-- Numbers, declared by one row. -/
def numberRules : (s : Sym) → List (ConstructorTyping.Rule Empty Name Empty typeArity (valueArity s))
  | .number _ => [⟨Fin.elim0, .closed .number⟩]
  | _ => []

/-- Booleans, declared by another. -/
def boolRules : (s : Sym) → List (ConstructorTyping.Rule Empty Name Empty typeArity (valueArity s))
  | .bool _ => [⟨Fin.elim0, .closed .bool⟩]
  | _ => []

/-- Row `0` declares numbers; every other row declares booleans. -/
def row (o : Nat) : Row Unit Empty Name Empty Sym typeArity valueArity :=
  if o = 0 then ⟨numberRules, []⟩ else ⟨boolRules, []⟩

def rows : List Nat := [0, 1, 2]

theorem symbols_leaf (s : Sym) : symbols (leaf s) = [s] := rfl

abbrev Rows := rowStep (U := Unit) (P := Empty) (Q := Name) (C := Empty) (Sym := Sym)
  (typeArity := typeArity) (valueArity := valueArity) trivial rows row

/-- Check `1 ∈ Number` and make the evidence row `5`. -/
def check : RowFiring Name Empty Sym typeArity valueArity Nat PUnit :=
  ⟨⟨[], [], [5]⟩, [], [(leaf (.number 1), .closed .number)]⟩

/-- Replace the boolean row `1` by row `2`: a declaration edit. -/
def unrelatedEdit : RowFiring Name Empty Sym typeArity valueArity Nat PUnit :=
  ⟨⟨[1], [], [2]⟩, [], []⟩

/-- Retract the number row `0`. -/
def relatedEdit : RowFiring Name Empty Sym typeArity valueArity Nat PUnit :=
  ⟨⟨[0], [], []⟩, [], []⟩

def start : Configuration PUnit Nat := ⟨[], {0, 1}⟩

theorem number_checked (W : Finset Nat) (present : 0 ∈ W) :
    Checked rows row check W := by
  intro c member
  rw [List.mem_singleton.mp member]
  exact DeclarationTyping.HasType.constructor (declarations := view rows row) (context := W)
    (symbol := .number 1) (children := Fin.elim0) ⟨Fin.elim0, .closed .number⟩
    (List.mem_flatMap.mpr ⟨0, List.mem_filter.mpr ⟨by simp [rows], decide_eq_true present⟩,
      by simp [row, numberRules]⟩) Empty.elim (fun i => i.elim0)

theorem number_unchecked (W : Finset Nat) (absent : 0 ∉ W) :
    ¬ Checked rows row check W := by
  intro checked
  have typed := checked _ (List.mem_singleton.mpr rfl)
  rcases (DeclarationTyping.hasType_node_iff (view rows row) W (.number 1) Fin.elim0 _).1 typed with
    ⟨rule, present, _⟩ | ⟨fact, present, _⟩
  · obtain ⟨o, kept, declared⟩ := List.mem_flatMap.mp present
    obtain ⟨_, inW⟩ := List.mem_filter.mp kept
    by_cases zero : o = 0
    · subst zero
      exact absent (of_decide_eq_true inW)
    · simp [row, zero, boolRules] at declared
  · obtain ⟨o, _, declared⟩ := List.mem_flatMap.mp present
    by_cases zero : o = 0 <;> simp [row, zero] at declared

theorem check_admitted : (Rows).Admits (s := start) check := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 5⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨PUnit.unit, PUnit.unit,
    fun _ _ => rfl⟩, fun _ _ _ => number_checked _ (by simp [start])⟩ <;>
    simp [check, Selection.commit, start]

def afterCheck : Configuration PUnit Nat := (Rows).result (s := start) check check_admitted

theorem afterCheck_present : afterCheck.present = {0, 1, 5} := by
  show fire {0, 1} _ = _
  decide

theorem unrelatedEdit_admitted : (Rows).Admits (s := afterCheck) unrelatedEdit := by
  refine ⟨⟨List.nodup_singleton 1, List.nodup_singleton 2⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨PUnit.unit, PUnit.unit,
    fun _ _ => rfl⟩, fun _ _ _ c member => by cases member⟩ <;>
    simp [unrelatedEdit, Selection.commit, afterCheck_present]

def afterEdit : Configuration PUnit Nat := (Rows).result (s := afterCheck) unrelatedEdit unrelatedEdit_admitted

theorem afterEdit_present : afterEdit.present = {0, 2, 5} := by
  show fire afterCheck.present _ = _
  rw [afterCheck_present]
  decide

/-- Read the evidence row `5` instead of checking again, and make the answer `6`. -/
def reuse : RowFiring Name Empty Sym typeArity valueArity Nat PUnit :=
  ⟨⟨[], [5], [6]⟩, [], []⟩

theorem reuse_admitted : (Rows).Admits (s := afterEdit) reuse := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 6⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨PUnit.unit, PUnit.unit,
    fun _ _ => rfl⟩, fun _ _ _ c member => by cases member⟩ <;>
    simp [reuse, Selection.commit, afterEdit_present]

/-- **The evidence run**: check `1 ∈ Number` and make the evidence row, edit an unrelated
declaration, then read the evidence row without checking. -/
def evidenceRun : (Rows).Run start :=
  .cons check check_admitted (.cons unrelatedEdit unrelatedEdit_admitted
    (.cons reuse reuse_admitted (.nil _)))

/-- **The unrelated edit touches the coarse region and not the fine one.** -/
theorem unrelated_edit :
    (∃ o ∈ rows, Interface.Step.Writes unrelatedEdit.selection o) ∧
      ∀ o ∈ fineRegion rows row (leaf (.number 1)), ¬ Interface.Step.Writes unrelatedEdit.selection o := by
  refine ⟨⟨1, by simp [rows], .inl (List.mem_singleton.mpr rfl)⟩, ?_⟩
  rintro o ⟨_, (⟨s, occurs, declared⟩ | facts)⟩ writes
  · have same : s = .number 1 := by simpa [symbols_leaf] using occurs
    subst same
    have ne : o = 0 := by
      by_contra other
      simp [row, other, boolRules] at declared
    subst ne
    simp [Interface.Step.Writes, unrelatedEdit] at writes
  · by_cases zero : o = 0 <;> simp [row, zero] at facts

/-- **The membership survives the run**, by the reuse theorem; the generation counter would have
discarded it. -/
theorem evidence_run_keeps_membership : Checked rows row check evidenceRun.last.present := by
  refine reuse_sound trivial rows row check (number_checked _ (by simp [start])) evidenceRun rfl ?_
  intro x member o inside writes
  obtain ⟨c, cMember, cInside⟩ := inside
  rw [List.mem_singleton.mp cMember] at cInside
  simp only [evidenceRun, Interface.Step.Run.word, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have five : o = 5 := by simpa [Interface.Step.Writes, check] using writes
    subst five
    exact absurd cInside.1 (by simp [rows])
  · exact (unrelated_edit.2 o cInside) writes
  · have six : o = 6 := by simpa [Interface.Step.Writes, reuse] using writes
    subst six
    exact absurd cInside.1 (by simp [rows])

/-- **Writing the fine region breaks the membership.** -/
theorem related_edit_breaks :
    0 ∈ fineRegion rows row (leaf (.number 1)) ∧ Interface.Step.Writes relatedEdit.selection 0 ∧
      Checked rows row check start.present ∧
      ¬ Checked rows row check (fire start.present (relatedEdit.selection.commit (T := Unit))) := by
  refine ⟨⟨by simp [rows], .inl ⟨.number 1, by simp [symbols_leaf], by simp [row, numberRules]⟩⟩,
    .inl (List.mem_singleton.mpr rfl), number_checked _ (by simp [start]), number_unchecked _ ?_⟩
  decide

end EvidenceControls

#print axioms guard_run
#print axioms member_inside
#print axioms fineGuards
#print axioms coarseGuards
#print axioms reuse_sound
#print axioms generation_sound
#print axioms EvidenceControls.check_admitted
#print axioms EvidenceControls.unrelated_edit
#print axioms EvidenceControls.evidence_run_keeps_membership
#print axioms EvidenceControls.related_edit_breaks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingEvidence
