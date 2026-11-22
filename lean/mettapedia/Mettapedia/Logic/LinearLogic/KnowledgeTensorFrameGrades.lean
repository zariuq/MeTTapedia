import Mathlib.Data.Multiset.Filter
import Mettapedia.Logic.LinearLogic.KnowledgeTensor

/-!
# Checks that read the residual frame, and where the tensor reading stops

A check reads the knowledge after the tell and the residual frame: the atoms the firing neither
takes nor reads. Absence and counting are such checks. They are stable under refinement of the
knowledge (`check_mono`) and need not be stable under growth of the frame.

## The boundary

* `HomomorphicReading.frame_stable`: if the runs of a checked system are the proofs of a tensor
  logic over a knowledge zone, along any translation of knowledge and any additive translation of
  resources, then its reachability is stable under every frame.
* `HomomorphicReading.false_of_frame_failure`: so one firing that a frame disables excludes every
  such reading. The controls file gives the absence and the counting instance.

## What restores a reading

* `Proves` grades a proof by the frames it admits. Identity admits every frame, a leaf admits the
  frames its check accepts, framing translates the grade and cut conjoins the grades.
  `run_iff_proves`: a run exists exactly when a proof exists whose grade admits the empty frame.
  `Proves.run` is the frame law relative to the grade.
* `derives_iff_proves_all_frames`: the tensor logic is exactly the fragment of proofs whose grade
  accepts every frame.
* `Run.frame_outside`: when the checks read the frame only inside a region, every run is stable
  under frames outside that region.
* `run_iff_cells`: the one-cell reading holds the whole linear zone as one atom and turns every
  check into a guard on that value. It is exact for every checked system, and it has no frame law
  for atoms at all (`cell_not_additive`). Exactness without additivity therefore isolates nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule uK' uAtom' uRule'

/-- Declared transitions whose check reads the residual frame. -/
structure CheckedSystem (K : Type uK) (Atom : Type uAtom) (Rule : Type uRule) [SemilatticeInf K] where
  take : Rule → Multiset Atom
  read : Rule → Multiset Atom
  make : Rule → Multiset Atom
  tell : Rule → K
  check : Rule → K → Multiset Atom → Prop
  check_mono : ∀ (declaration : Rule) {stronger weaker : K} (frame : Multiset Atom),
    stronger ≤ weaker → check declaration weaker frame → check declaration stronger frame

namespace CheckedSystem

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : CheckedSystem K Atom Rule)

def premises (declaration : Rule) : Multiset Atom := sys.take declaration + sys.read declaration

def conclusions (declaration : Rule) : Multiset Atom := sys.read declaration + sys.make declaration

/-- One firing, over its complete residual frame, which the check reads. -/
abbrev Fires (declaration : Rule) (k : K) (Γ : Multiset Atom) (k' : K) (Γ' : Multiset Atom) : Prop :=
  ∃ frame : Multiset Atom, Γ = sys.premises declaration + frame ∧
    sys.check declaration (k ⊓ sys.tell declaration) frame ∧ k' = k ⊓ sys.tell declaration ∧
    Γ' = sys.conclusions declaration + frame

inductive Run : K → Multiset Atom → List Rule → K → Multiset Atom → Prop
  | done (k : K) (Γ : Multiset Atom) : Run k Γ [] k Γ
  | fire {declaration : Rule} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {rest : List Rule} :
      sys.Fires declaration k Γ k₁ Γ₁ → Run k₁ Γ₁ rest k' Γ' → Run k Γ (declaration :: rest) k' Γ'

/-- Proofs graded by the frames they accept. -/
inductive Proves : K → Multiset Atom → (Multiset Atom → Prop) → List Rule → K → Multiset Atom → Prop
  | identity (k : K) (Γ : Multiset Atom) : Proves k Γ (fun _ => True) [] k Γ
  | rule (declaration : Rule) (k : K) :
      Proves k (sys.premises declaration)
        (fun frame => sys.check declaration (k ⊓ sys.tell declaration) frame) [declaration]
        (k ⊓ sys.tell declaration) (sys.conclusions declaration)
  | frame {k k' : K} {Γ Γ' : Multiset Atom} {grade : Multiset Atom → Prop} {uses : List Rule}
      (extra : Multiset Atom) :
      Proves k Γ grade uses k' Γ' → Proves k (Γ + extra) (fun frame => grade (extra + frame)) uses k' (Γ' + extra)
  | strengthen {k k' : K} {Γ Γ' : Multiset Atom} {grade : Multiset Atom → Prop} {uses : List Rule}
      (more : K) :
      Proves k Γ grade uses k' Γ' → Proves (k ⊓ more) Γ grade uses (k' ⊓ more) Γ'
  | cut {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {early late : Multiset Atom → Prop}
      {first second : List Rule} :
      Proves k Γ early first k₁ Γ₁ → Proves k₁ Γ₁ late second k' Γ' →
        Proves k Γ (fun frame => early frame ∧ late frame) (first ++ second) k' Γ'
  | restrict {k k' : K} {Γ Γ' : Multiset Atom} {grade stricter : Multiset Atom → Prop}
      {uses : List Rule} (implies : ∀ frame, stricter frame → grade frame) :
      Proves k Γ grade uses k' Γ' → Proves k Γ stricter uses k' Γ'

/-- The checks read the frame only inside a region. -/
def ReadsOnly (region : Atom → Prop) [DecidablePred region] : Prop :=
  ∀ (declaration : Rule) (k : K) (frame : Multiset Atom),
    sys.check declaration k frame ↔ sys.check declaration k (frame.filter region)

variable {sys}

theorem Fires.strengthen {declaration : Rule} {k k' : K} {Γ Γ' : Multiset Atom} (more : K)
    (fires : sys.Fires declaration k Γ k' Γ') :
    sys.Fires declaration (k ⊓ more) Γ (k' ⊓ more) Γ' := by
  obtain ⟨frame, source, checked, knowledge, target⟩ := fires
  refine ⟨frame, source, sys.check_mono declaration frame (inf_le_inf_right _ inf_le_left) checked, ?_, target⟩
  rw [knowledge, inf_right_comm]

/-- A firing is a function of its declaration and its source. -/
theorem Fires.deterministic {declaration : Rule} {k k₁ k₂ : K} {Γ Γ₁ Γ₂ : Multiset Atom}
    (one : sys.Fires declaration k Γ k₁ Γ₁) (two : sys.Fires declaration k Γ k₂ Γ₂) :
    k₁ = k₂ ∧ Γ₁ = Γ₂ := by
  obtain ⟨frame, source, _, knowledge, target⟩ := one
  obtain ⟨other, source', _, knowledge', target'⟩ := two
  have same : frame = other := add_left_cancel (source.symm.trans source')
  exact ⟨knowledge.trans knowledge'.symm, by rw [target, target', same]⟩

theorem Fires.refines {declaration : Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (fires : sys.Fires declaration k Γ k' Γ') : k' ≤ k := by
  obtain ⟨_, _, _, knowledge, _⟩ := fires
  rw [knowledge]
  exact inf_le_left

theorem Run.append {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {first second : List Rule}
    (one : sys.Run k Γ first k₁ Γ₁) (two : sys.Run k₁ Γ₁ second k' Γ') :
    sys.Run k Γ (first ++ second) k' Γ' := by
  induction one with
  | done k Γ => exact two
  | fire fires later ih => exact Run.fire fires (ih two)

/-- Knowledge only refines along a run, whatever its checks. -/
theorem Run.refines {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') : k' ≤ k := by
  induction run with
  | done k Γ => exact le_rfl
  | fire fires later ih => exact ih.trans (Fires.refines fires)

theorem Run.strengthen {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (more : K)
    (run : sys.Run k Γ uses k' Γ') : sys.Run (k ⊓ more) Γ uses (k' ⊓ more) Γ' := by
  induction run with
  | done k Γ => exact Run.done (k ⊓ more) Γ
  | fire fires later ih => exact Run.fire (Fires.strengthen more fires) ih

/-! ## Graded proofs and runs -/

/-- **The frame law relative to the grade.** A proof runs over every frame its grade admits. -/
theorem Proves.run {k k' : K} {Γ Γ' : Multiset Atom} {grade : Multiset Atom → Prop} {uses : List Rule}
    (proof : sys.Proves k Γ grade uses k' Γ') :
    ∀ frame : Multiset Atom, grade frame → sys.Run k (Γ + frame) uses k' (Γ' + frame) := by
  induction proof with
  | identity k Γ =>
      intro frame _
      exact Run.done k (Γ + frame)
  | rule declaration k =>
      intro frame checked
      have fires : sys.Fires declaration k (sys.premises declaration + frame)
          (k ⊓ sys.tell declaration) (sys.conclusions declaration + frame) :=
        ⟨frame, rfl, checked, rfl, rfl⟩
      exact Run.fire fires (Run.done _ _)
  | frame extra prior ih =>
      intro frame graded
      simpa only [add_assoc] using ih (extra + frame) graded
  | strengthen more prior ih =>
      intro frame graded
      exact Run.strengthen more (ih frame graded)
  | cut first second ihFirst ihSecond =>
      intro frame graded
      exact Run.append (ihFirst frame graded.1) (ihSecond frame graded.2)
  | restrict implies prior ih =>
      intro frame graded
      exact ih frame (implies frame graded)

/-- A run is a proof whose grade admits the empty frame. -/
theorem Run.proves {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') :
    ∃ grade : Multiset Atom → Prop, grade 0 ∧ sys.Proves k Γ grade uses k' Γ' := by
  induction run with
  | done k Γ => exact ⟨fun _ => True, trivial, Proves.identity k Γ⟩
  | @fire declaration k k₁ k' Γ Γ₁ Γ' rest fires later ih =>
      obtain ⟨frame, source, checked, knowledge, target⟩ := fires
      obtain ⟨grade, atZero, proof⟩ := ih
      subst source knowledge target
      exact ⟨fun extra => sys.check declaration (k ⊓ sys.tell declaration) (frame + extra) ∧ grade extra,
        ⟨by simpa only [add_zero] using checked, atZero⟩,
        Proves.cut (Proves.frame frame (Proves.rule declaration k)) proof⟩

/-- **Runs correspond to graded proofs**, for every check. -/
theorem run_iff_proves (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Run k Γ uses k' Γ' ↔
      ∃ grade : Multiset Atom → Prop, grade 0 ∧ sys.Proves k Γ grade uses k' Γ' := by
  constructor
  · exact Run.proves
  · rintro ⟨grade, atZero, proof⟩
    simpa only [add_zero] using Proves.run proof 0 atZero

/-! ## Regions -/

/-- **The frame law outside a region.** Checks that read the frame only inside a region are
stable under frames outside it. -/
theorem Run.frame_outside (region : Atom → Prop) [DecidablePred region] (regional : sys.ReadsOnly region)
    {extra : Multiset Atom} (outside : ∀ atom ∈ extra, ¬ region atom)
    {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (run : sys.Run k Γ uses k' Γ') :
    sys.Run k (Γ + extra) uses k' (Γ' + extra) := by
  induction run with
  | done k Γ => exact Run.done k (Γ + extra)
  | fire fires later ih =>
      obtain ⟨frame, source, checked, knowledge, target⟩ := fires
      have grown : (frame + extra).filter region = frame.filter region := by
        rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr outside, add_zero]
      have inside := (regional _ _ _).mp checked
      rw [← grown] at inside
      have still := (regional _ _ (frame + extra)).mpr inside
      exact Run.fire ⟨frame + extra, by rw [source, add_assoc], still, knowledge,
        by rw [target, add_assoc]⟩ ih

end CheckedSystem

/-! ## The tensor logic inside the graded calculus -/

namespace System

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]

/-- A guard on knowledge is a check that ignores the frame. -/
def checked (sys : System K Atom Rule) : CheckedSystem K Atom Rule where
  take := sys.take
  read := sys.read
  make := sys.make
  tell := sys.tell
  check declaration k _ := sys.guard declaration k
  check_mono := fun declaration _ _ _ refines holds => sys.guard_mono declaration refines holds

variable {sys : System K Atom Rule}

theorem checked_run_iff (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.checked.Run k Γ uses k' Γ' ↔ sys.Run k Γ uses k' Γ' := by
  constructor
  · intro run
    induction run with
    | done k Γ => exact Run.done k Γ
    | fire fires later ih => exact Run.fire fires ih
  · intro run
    induction run with
    | done k Γ => exact CheckedSystem.Run.done k Γ
    | fire fires later ih => exact CheckedSystem.Run.fire fires ih

/-- **The tensor logic is the fragment of proofs whose grade accepts every frame.** -/
theorem derives_iff_proves_all_frames (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Derives k Γ uses k' Γ' ↔ sys.checked.Proves k Γ (fun _ => True) uses k' Γ' := by
  constructor
  · intro proof
    induction proof with
    | identity k Γ => exact CheckedSystem.Proves.identity k Γ
    | rule declaration k asked =>
        exact CheckedSystem.Proves.restrict (fun _ _ => asked) (CheckedSystem.Proves.rule declaration k)
    | frame extra prior ih => exact CheckedSystem.Proves.frame extra ih
    | strengthen more prior ih => exact CheckedSystem.Proves.strengthen more ih
    | cut first second ihFirst ihSecond =>
        have joined := CheckedSystem.Proves.cut ihFirst ihSecond
        exact CheckedSystem.Proves.restrict (fun _ _ => And.intro trivial trivial) joined
  · intro proof
    have run : sys.checked.Run k Γ uses k' Γ' := by
      simpa only [add_zero] using CheckedSystem.Proves.run proof 0 trivial
    exact Run.derives ((checked_run_iff k k' Γ Γ' uses).mp run)

end System

/-! ## No additive reading of a frame-sensitive check -/

/-- A reading of a checked system in a tensor logic over a knowledge zone. Knowledge is translated
by any function, resources by an additive map, and runs are exactly proofs. -/
structure HomomorphicReading {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
    (sys : CheckedSystem K Atom Rule) {K' : Type uK'} {Atom' : Type uAtom'} {Rule' : Type uRule'}
    [SemilatticeInf K'] (logic : System K' Atom' Rule') where
  knowledge : K → K'
  resources : Multiset Atom →+ Multiset Atom'
  runs_iff_proofs : ∀ (k k' : K) (Γ Γ' : Multiset Atom),
    (∃ uses, sys.Run k Γ uses k' Γ') ↔
      ∃ uses, logic.Derives (knowledge k) (resources Γ) uses (knowledge k') (resources Γ')

namespace HomomorphicReading

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  {sys : CheckedSystem K Atom Rule} {K' : Type uK'} {Atom' : Type uAtom'} {Rule' : Type uRule'}
  [SemilatticeInf K'] {logic : System K' Atom' Rule'}

/-- **A system with an additive tensor reading has reachability stable under every frame.** -/
theorem frame_stable (reading : HomomorphicReading sys logic) {k k' : K} {Γ Γ' : Multiset Atom}
    (reaches : ∃ uses, sys.Run k Γ uses k' Γ') (extra : Multiset Atom) :
    ∃ uses, sys.Run k (Γ + extra) uses k' (Γ' + extra) := by
  obtain ⟨uses, proof⟩ := (reading.runs_iff_proofs k k' Γ Γ').mp reaches
  refine (reading.runs_iff_proofs k k' (Γ + extra) (Γ' + extra)).mpr ⟨uses, ?_⟩
  rw [map_add, map_add]
  exact System.Derives.frame (reading.resources extra) proof

/-- **The boundary.** One reachability that a frame disables excludes every additive reading. -/
theorem false_of_frame_failure (reading : HomomorphicReading sys logic) {k k' : K} {Γ Γ' : Multiset Atom}
    (reaches : ∃ uses, sys.Run k Γ uses k' Γ') {extra : Multiset Atom}
    (disabled : ¬ ∃ uses, sys.Run k (Γ + extra) uses k' (Γ' + extra)) : False :=
  disabled (reading.frame_stable reaches extra)

end HomomorphicReading

/-! ## The one-cell reading -/

namespace CheckedSystem

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : CheckedSystem K Atom Rule)

/-- The whole linear zone held as one atom. A use names its declaration and its residual frame,
and the check becomes a guard on that value. -/
def cells : System K (Multiset Atom) (Rule × Multiset Atom) where
  take use := {sys.premises use.1 + use.2}
  read _ := 0
  make use := {sys.conclusions use.1 + use.2}
  tell use := sys.tell use.1
  guard use k := sys.check use.1 k use.2
  guard_mono := fun use _ _ refines holds => sys.check_mono use.1 use.2 refines holds

variable {sys}

theorem cells_premises (use : Rule × Multiset Atom) :
    sys.cells.premises use = {sys.premises use.1 + use.2} := add_zero _

theorem cells_conclusions (use : Rule × Multiset Atom) :
    sys.cells.conclusions use = {sys.conclusions use.1 + use.2} := zero_add _

theorem cell_fires {declaration : Rule} {k k' : K} {Γ Γ' frame : Multiset Atom}
    (source : Γ = sys.premises declaration + frame)
    (checked : sys.check declaration (k ⊓ sys.tell declaration) frame)
    (knowledge : k' = k ⊓ sys.tell declaration) (target : Γ' = sys.conclusions declaration + frame) :
    sys.cells.Fires (declaration, frame) k {Γ} k' {Γ'} := by
  refine ⟨0, ?_, checked, knowledge, ?_⟩
  · simp only [cells_premises, add_zero, source]
  · simp only [cells_conclusions, add_zero, target]

/-- A firing of the one-cell reading from one cell is a firing of the system, and leaves one
cell. -/
theorem fires_of_cell {use : Rule × Multiset Atom} {k k' : K} {Γ : Multiset Atom}
    {after : Multiset (Multiset Atom)} (fires : sys.cells.Fires use k {Γ} k' after) :
    ∃ Γ' : Multiset Atom, after = {Γ'} ∧ sys.Fires use.1 k Γ k' Γ' := by
  obtain ⟨others, source, checked, knowledge, target⟩ := fires
  rw [cells_premises, Multiset.singleton_add] at source
  obtain ⟨same, empty⟩ := (Multiset.singleton_eq_cons_iff others).mp source
  subst empty
  rw [cells_conclusions, add_zero] at target
  exact ⟨sys.conclusions use.1 + use.2, target, use.2, same, checked, knowledge, rfl⟩

/-- **The one-cell reading is exact for every checked system.** -/
theorem run_iff_cells (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Run k Γ uses k' Γ' ↔
      ∃ cellUses : List (Rule × Multiset Atom), cellUses.map Prod.fst = uses ∧
        sys.cells.Run k {Γ} cellUses k' {Γ'} := by
  constructor
  · intro run
    induction run with
    | done k Γ => exact ⟨[], rfl, System.Run.done k {Γ}⟩
    | fire fires later ih =>
        obtain ⟨frame, source, checked, knowledge, target⟩ := fires
        obtain ⟨cellUses, same, cellRun⟩ := ih
        exact ⟨(_, frame) :: cellUses, by simp only [List.map_cons, same],
          System.Run.fire (cell_fires source checked knowledge target) cellRun⟩
  · rintro ⟨cellUses, rfl, cellRun⟩
    have general : ∀ {start finish : Multiset (Multiset Atom)} {k k' : K}
        {cellUses : List (Rule × Multiset Atom)}, sys.cells.Run k start cellUses k' finish →
        ∀ Γ Γ' : Multiset Atom, start = {Γ} → finish = {Γ'} →
          sys.Run k Γ (cellUses.map Prod.fst) k' Γ' := by
      intro start finish k k' cellUses cellRun
      induction cellRun with
      | done k start =>
          intro Γ Γ' atStart atFinish
          have same : Γ = Γ' := Multiset.singleton_inj.mp (atStart.symm.trans atFinish)
          subst same
          exact Run.done k Γ
      | fire fires later ih =>
          intro Γ Γ' atStart atFinish
          subst atStart
          obtain ⟨middle, atMiddle, step⟩ := fires_of_cell fires
          exact Run.fire step (ih middle Γ' atMiddle atFinish)
    exact general cellRun Γ Γ' rfl rfl

/-- The one-cell translation of resources is not additive: a frame is not a second cell. -/
theorem cell_not_additive (Γ extra : Multiset Atom) :
    ({Γ + extra} : Multiset (Multiset Atom)) ≠ {Γ} + {extra} := by
  intro same
  have sizes := congrArg Multiset.card same
  rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_singleton, Multiset.card_singleton] at sizes
  exact absurd sizes (by decide)

end CheckedSystem

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
