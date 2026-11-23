import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality

/-!
# Regional conversion in the rule syntax

A region chooses its conversion relation on the common terms of each
frame. An assignment still acts on all terms at once. Store the region
with the term so that a firing can ask different equalities in different
regions, without changing which assignments it quantifies over.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)

universe uO uT uH uR uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {Region : Type uR}

/-- Each region has its own substitution-stable equivalence. -/
structure RegionalEquality (base : Frames Tm Hom) (Region : Type uR) where
  conversion : (region : Region) → (a : Obj) → Setoid (Tm a)
  preserves : ∀ (region : Region) {a b : Obj} (σ : Hom a b) {left right : Tm a},
    (conversion region a).r left right →
      (conversion region b).r (base.act σ left) (base.act σ right)

namespace RegionalEquality

variable {base : Frames Tm Hom} (views : RegionalEquality base Region)

/-- Keep physical regions rigid and use their conversion on payloads. -/
def frames : Frames (fun a => Region × Tm a) Hom where
  E {a} left right := left.1 = right.1 ∧ (views.conversion left.1 a).r left.2 right.2
  equivalence a := by
    constructor
    · rintro ⟨region, term⟩
      exact ⟨rfl, (views.conversion region a).iseqv.refl term⟩
    · rintro ⟨region, left⟩ ⟨_, right⟩ ⟨rfl, same⟩
      exact ⟨rfl, (views.conversion region a).iseqv.symm same⟩
    · rintro ⟨region, left⟩ ⟨_, middle⟩ ⟨_, right⟩ ⟨rfl, first⟩ ⟨rfl, second⟩
      exact ⟨rfl, (views.conversion region a).iseqv.trans first second⟩
  act σ term := (term.1, base.act σ term.2)
  id := base.id
  comp := base.comp
  act_id term := Prod.ext rfl (base.act_id term.2)
  act_comp g f term := Prod.ext rfl (base.act_comp g f term.2)
  preserves := by
    intro a b σ left right same
    exact ⟨same.1, views.preserves _ σ same.2⟩

/-- The region of a label is invariant under every frame assignment. -/
@[simp] theorem region_act {a b : Obj} (σ : Hom a b) (term : Region × Tm a) :
    (views.frames.act σ term).1 = term.1 := rfl

/-- A mixed store has one common assignment satisfying each equation in
its own region. -/
theorem models_iff {a b : Obj} (σ : Hom a b) (store : EquationStore (Region × Tm a)) :
    views.frames.Models σ store ↔
      ∀ e ∈ store, e.1.1 = e.2.1 ∧
        (views.conversion e.1.1 b).r (base.act σ e.1.2) (base.act σ e.2.2) :=
  Iff.rfl

/-- A query finds the present rows in its region whose payloads convert
at the given solution. -/
theorem mem_matchesAt {a b : Obj} {O : Type uOcc} (σ : Hom a b) (row : O → Region × Tm a)
    (present : Finset O) (region : Region) (pattern : Tm a) (o : O) :
    o ∈ RuleSyntax.matchesAt views.frames σ row present (region, pattern) ↔
      o ∈ present ∧ region = (row o).1 ∧
        (views.conversion region b).r (base.act σ pattern) (base.act σ (row o).2) := by
  rw [RuleSyntax.mem_matchesAt]
  rfl

section Firing

variable {O : Type uOcc} [DecidableEq O]
  {E : Extensions.{uO, uH, uE} Hom} {P : Program (fun a => Region × Tm a)}
  {s : State (fun a => Region × Tm a) O} {f : Firing O E P s.frame}

/-- Only a row at the declared region can supply an opened take. -/
theorem taken_region (admitted : (step views.frames O E P).Admits (s := s) f)
    {pattern : Region × Tm (E.target f.ext)} {o : O}
    (selected : (pattern, o) ∈ (f.opened views.frames).take.zip f.selection.taken) :
    pattern.1 = (s.label o).1 := by
  obtain ⟨b, σ, solved⟩ := admitted.2.2.1
  exact (f.take_solved (X := views.frames) solved selected).1

/-- The same regional constraint holds for non-consuming reads. -/
theorem read_region (admitted : (step views.frames O E P).Admits (s := s) f)
    {pattern : Region × Tm (E.target f.ext)} {o : O}
    (selected : (pattern, o) ∈ (f.opened views.frames).read.zip f.selection.read) :
    pattern.1 = (s.label o).1 := by
  obtain ⟨b, σ, solved⟩ := admitted.2.2.1
  exact (f.read_solved (X := views.frames) solved selected).1

/-- At a fixed knowledge cut, a change outside all queried regions and
selected identities preserves admission, provided the opening stays fresh. -/
theorem admits_iff_of_other_regions {W : Finset O}
    (touched : ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.read ∨ o ∈ f.selection.made) →
      (o ∈ s.present ↔ o ∈ W))
    (apart : ∀ p ∈ f.queryPatterns views.frames, ∀ o, ¬ (o ∈ s.present ↔ o ∈ W) →
      p.1 ≠ (s.label o).1)
    (fresh : f.Fresh views.frames s) (fresh' : f.Fresh views.frames (s.withPresent W)) :
    (step views.frames O E P).Admits (s := s) f ↔
      (step views.frames O E P).Admits (s := s.withPresent W) f := by
  apply RuleSyntax.admits_iff_of_outsideRegions ?_ fresh fresh'
  exact ⟨touched, fun _ _ _ p pattern o changed same => apart p pattern o changed same.1⟩

end Firing

section Runs

variable {O : Type uOcc} [DecidableEq O]
  {E : Extensions.{uO, uH, uE} Hom} {P : Program (fun a => Region × Tm a)}
  {s : State (fun a => Region × Tm a) O}

local notation "system" => Interface.Step.Standard.toStep (step views.frames O E P)

/-- A solution at the end validates each original equation in its
original region after the composed assignments of the run. -/
theorem models_start_of_run (run : (system).Run s) {b : Obj}
    (σ : Hom ((system).frame run.last) b) (solved : views.frames.Models σ ((system).knowledge run.last))
    {e : Equation (Region × Tm s.frame)} (member : e ∈ s.knowledge) :
    e.1.1 = e.2.1 ∧
      (views.conversion e.1.1 b).r
        (base.act (base.comp σ run.toLast) e.1.2)
        (base.act (base.comp σ run.toLast) e.2.2) :=
  (views.models_iff _ _).mp (run.models_start σ solved) e member

end Runs

/-- Substitution stability is the exact boundary for using the same
assignments and retaining rigid region tags. Necessity applies to any
frame action with the prescribed term action and regional equality. -/
theorem frame_exists_iff (base : Frames Tm Hom)
    (conversion : (region : Region) → (a : Obj) → Setoid (Tm a)) :
    (∃ Y : Frames (fun a => Region × Tm a) Hom,
      (∀ {a b : Obj} (σ : Hom a b) (term : Region × Tm a),
        Y.act σ term = (term.1, base.act σ term.2)) ∧
      (∀ {a : Obj} (left right : Region × Tm a),
        Y.E left right ↔ left.1 = right.1 ∧ (conversion left.1 a).r left.2 right.2)) ↔
      (∀ (region : Region) {a b : Obj} (σ : Hom a b) {left right : Tm a},
        (conversion region a).r left right →
          (conversion region b).r (base.act σ left) (base.act σ right)) := by
  constructor
  · rintro ⟨Y, acted, compared⟩ region a b σ left right equal
    have source := (compared (region, left) (region, right)).mpr ⟨rfl, equal⟩
    have target := Y.preserves σ source
    rw [acted σ (region, left), acted σ (region, right)] at target
    exact ((compared _ _).mp target).2
  · intro stable
    let regional : RegionalEquality base Region := ⟨conversion, stable⟩
    exact ⟨regional.frames, fun _ _ => rfl, fun _ _ => Iff.rfl⟩

end RegionalEquality

namespace RegionalEquality.Incomparable

/-! A single unknown ranges over four constants. The three views are
the two partitions and their least common coarsening. -/

inductive View where
  | first | second | join

abbrev Term := Option (Fin 4)

private def assign (value : Term) : Term → Term
  | none => value
  | some letter => some letter

private def base : Frames (fun _ : Unit => Term) (fun _ _ => Term) where
  E := Eq
  equivalence _ := eq_equivalence
  act := assign
  id _ := none
  comp := assign
  act_id term := by cases term <;> rfl
  act_comp _ _ term := by cases term <;> rfl
  preserves := by
    intro a b value left right same
    exact congrArg (assign value) same

def code (view : View) : Term → Nat
  | none => 4
  | some letter => match view with
    | .first => letter.val / 2
    | .second => if letter.val = 2 then 1 else letter.val
    | .join => 0

private theorem none_apart (view : View) (letter : Fin 4) :
    code view none ≠ code view (some letter) := by
  cases view <;> fin_cases letter <;> decide

def views : RegionalEquality base View where
  conversion view _ :=
    ⟨fun t u => code view t = code view u, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  preserves := by
    intro view a b value left right same
    change code view left = code view right at same
    change code view (assign value left) = code view (assign value right)
    cases left with
    | none =>
      cases right with
      | none => rfl
      | some letter => exact (none_apart view letter same).elim
    | some letter =>
      cases right with
      | none => exact (none_apart view letter same.symm).elim
      | some _ => exact same

/-- The join identifies all four constants, and each identification is
forced by the chain a to b to c to d in the two given views. -/
theorem least_join (relation : Setoid Term)
    (first : ∀ {t u}, code .first t = code .first u → relation.r t u)
    (second : ∀ {t u}, code .second t = code .second u → relation.r t u)
    {t u : Term} (joined : code .join t = code .join u) : relation.r t u := by
  have ab : relation.r (some 0) (some 1) := first rfl
  have bc : relation.r (some 1) (some 2) := second rfl
  have cd : relation.r (some 2) (some 3) := first rfl
  have fromA (letter : Fin 4) : relation.r (some 0) (some letter) := by
    fin_cases letter
    · exact relation.iseqv.refl _
    · exact ab
    · exact relation.iseqv.trans ab bc
    · exact relation.iseqv.trans ab (relation.iseqv.trans bc cd)
  cases t with
  | none =>
    cases u with
    | none => exact relation.iseqv.refl _
    | some letter => exact (none_apart .join letter joined).elim
  | some left =>
    cases u with
    | none => exact (none_apart .join left joined.symm).elim
    | some right => exact relation.iseqv.trans (relation.iseqv.symm (fromA left)) (fromA right)

theorem join_contains {view : View} {t u : Term} (related : code view t = code view u) :
    code .join t = code .join u := by
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some letter => exact (none_apart view letter related).elim
  | some letter =>
    cases u with
    | none => exact (none_apart view letter related.symm).elim
    | some _ => rfl

def equation (view : View) (letter : Fin 4) : EquationStore (View × Term) :=
  [((view, none), (view, some letter))]

private theorem equation_models (view : View) (letter : Fin 4) (value : Term) :
    views.frames.Models (a := ()) (b := ()) value (equation view letter) ↔
      code view value = code view (some letter) := by
  rw [views.models_iff]
  constructor
  · intro model
    exact (model ((view, none), (view, some letter)) (List.mem_singleton_self _)).2
  · intro same e member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rfl, same⟩

/-- Each projection, including the projection to the join, is solvable.
The original conjunction has no common assignment. -/
theorem separate_and_join_solve_joint_refutes :
    views.frames.Solvable (a := ()) (equation .first 0) ∧
    views.frames.Solvable (a := ()) (equation .second 3) ∧
    views.frames.Solvable (a := ()) (equation .join 0 ++ equation .join 3) ∧
    ¬ views.frames.Solvable (a := ()) (equation .first 0 ++ equation .second 3) := by
  refine ⟨⟨(), some 0, (equation_models _ _ _).mpr rfl⟩,
    ⟨(), some 3, (equation_models _ _ _).mpr rfl⟩, ?_, ?_⟩
  · refine ⟨(), some 0, (views.frames.models_append _ _ _).mpr
      ⟨(equation_models _ _ _).mpr rfl, (equation_models _ _ _).mpr rfl⟩⟩
  · rintro ⟨⟨⟩, answer, solved⟩
    obtain ⟨first, second⟩ := (views.frames.models_append _ _ _).mp solved
    have low := (equation_models _ _ _).mp first
    have high := (equation_models _ _ _).mp second
    cases answer with
    | none => exact none_apart .first 0 low
    | some letter => fin_cases letter <;> simp [code] at low high

end RegionalEquality.Incomparable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
