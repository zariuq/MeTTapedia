import Mathlib.CategoryTheory.Category.Preorder
import Mettapedia.Logic.LinearLogic.KnowledgeTensorZoned
import Mettapedia.Logic.LinearLogic.KnowledgeTensorLending
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrameGrades

/-!
# The fragments of the whole calculus

Each earlier system is an instance of the whole calculus, and its runs are exactly the runs of
that instance.

* `IndexedSystem.run_iff_zoned`: frames, no check, nothing lent.
* `System.runUnder_iff_zoned`, `System.run_iff_zoned`: one frame and no check, with a lent
  context or with nothing lent. One frame means that nothing is transported.
* `CheckedSystem.run_iff_zoned`: one frame, with checks. A check of the frame beside the read
  atoms is a check of every atom the firing does not take.

With `ZonedSystem.run_iff_proves`, every one of these runs is a graded proof of the whole
calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

open _root_.CategoryTheory

universe uF uH uK uAtom uRule u

/-- A family over the one frame. -/
abbrev Const (X : Type u) : Unit → Type u := fun _ => X

theorem map_snd_mk {Rule : Type uRule} (uses : List Rule) :
    (uses.map (Sigma.mk (β := Const Rule) ())).map (fun use => (use.2 : Rule)) = uses := by
  induction uses with
  | nil => rfl
  | cons declaration rest ih => simp only [List.map_cons, ih]

namespace ZonedSystem

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule} {sys : ZonedSystem Frame K Atom Rule}

theorem RunUnder.relent {a b : Frame} {lent other : Multiset (Atom a)} {k : K a}
    {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (same : lent = other)
    (run : sys.RunUnder a lent k Γ uses b along k' Γ') :
    sys.RunUnder a other k Γ uses b along k' Γ' := by
  subst same
  exact run

end ZonedSystem

/-! ## Frames without checks -/

namespace IndexedSystem

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule} (sys : IndexedSystem Frame K Atom Rule)

/-- No check: every context is accepted. -/
def zoned : ZonedSystem Frame K Atom Rule where
  toIndexedSystem := sys
  check := fun _ _ _ => True
  check_mono := fun _ _ _ _ _ _ => True.intro

variable {sys}

theorem zoned_firesUnder_zero_iff {a : Frame} (declaration : Rule a) (k : K a)
    (Γ : Multiset (Atom a)) (k' : K (sys.target declaration))
    (Γ' : Multiset (Atom (sys.target declaration))) :
    sys.zoned.FiresUnder 0 declaration k Γ k' Γ' ↔ sys.Fires declaration k Γ k' Γ' := by
  constructor
  · rintro ⟨frame, source, readable, asked, _, knowledge, target⟩
    change Γ = sys.take declaration + frame at source
    change sys.read declaration ≤ frame + 0 at readable
    change Γ' = sys.make declaration + sys.carried (sys.extend declaration) frame at target
    rw [add_zero] at readable
    obtain ⟨rest, split⟩ := Multiset.le_iff_exists_add.mp readable
    subst split
    refine ⟨rest, ?_, asked, knowledge, ?_⟩
    · rw [source, premises, add_assoc]
    · rw [target, conclusions, carried_add, ← add_assoc, add_comm (sys.make declaration)]
  · rintro ⟨rest, source, asked, knowledge, target⟩
    refine ⟨sys.read declaration + rest, ?_, ?_, asked, True.intro, knowledge, ?_⟩
    · show Γ = sys.take declaration + (sys.read declaration + rest)
      rw [source, premises, add_assoc]
    · show sys.read declaration ≤ sys.read declaration + rest + 0
      rw [add_zero]
      exact Multiset.le_add_right _ _
    · show Γ' = sys.make declaration +
        sys.carried (sys.extend declaration) (sys.read declaration + rest)
      rw [target, conclusions, carried_add, ← add_assoc, add_comm (sys.make declaration)]

theorem zoned_run_of_run {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (run : sys.Run a k Γ uses b along k' Γ') :
    sys.zoned.RunUnder a 0 k Γ uses b along k' Γ' := by
  induction run with
  | done a k Γ => exact ZonedSystem.RunUnder.done a 0 k Γ
  | fire fires later ih =>
      exact ZonedSystem.RunUnder.fire ((zoned_firesUnder_zero_iff _ _ _ _ _).mpr fires)
        (ZonedSystem.RunUnder.relent (carried_zero _).symm ih)

theorem run_of_zoned_run {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
    {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (run : sys.zoned.RunUnder a lent k Γ uses b along k' Γ') :
    lent = 0 → sys.Run a k Γ uses b along k' Γ' := by
  induction run with
  | done a lent k Γ =>
      intro _
      exact Run.done a k Γ
  | fire fires later ih =>
      intro empty
      subst empty
      exact Run.fire ((zoned_firesUnder_zero_iff _ _ _ _ _).mp fires) (ih (carried_zero _))

/-- **The frame-indexed runs are the runs of the whole calculus without checks and with nothing
lent.** -/
theorem run_iff_zoned {a b : Frame} (k : K a) (Γ : Multiset (Atom a)) (uses : List (Sigma Rule))
    (along : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)) :
    sys.Run a k Γ uses b along k' Γ' ↔ sys.zoned.RunUnder a 0 k Γ uses b along k' Γ' :=
  ⟨zoned_run_of_run, fun run => run_of_zoned_run run rfl⟩

end IndexedSystem

/-! ## One frame, no check -/

namespace System

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- One frame: nothing is transported and no name is born. -/
def zoned : ZonedSystem Unit (Const K) (Const Atom) (Const Rule) where
  know := fun _ k => k
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun _ atom => atom
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a
  extend := fun {a} _ => 𝟙 a
  take := fun declaration => sys.take declaration
  read := fun declaration => sys.read declaration
  make := fun declaration => sys.make declaration
  tell := fun declaration => sys.tell declaration
  guard := fun declaration k => sys.guard declaration k
  guard_mono := fun declaration _ _ refines holds => sys.guard_mono declaration refines holds
  check := fun _ _ _ => True
  check_mono := fun _ _ _ _ _ _ => True.intro

variable {sys}

theorem zoned_carried {a b : Unit} (step : a ⟶ b) (Γ : Multiset (Const Atom a)) :
    sys.zoned.carried step Γ = Γ :=
  Multiset.map_id' Γ

theorem zoned_firesUnder_iff {a : Unit} (lent : Multiset (Const Atom a)) (declaration : Const Rule a)
    (k : Const K a) (Γ : Multiset (Const Atom a)) (k' : Const K a) (Γ' : Multiset (Const Atom a)) :
    sys.zoned.FiresUnder lent declaration k Γ k' Γ' ↔ sys.FiresUnder lent declaration k Γ k' Γ' := by
  constructor
  · rintro ⟨frame, source, readable, asked, _, knowledge, target⟩
    refine ⟨frame, source, readable, asked, knowledge, ?_⟩
    rw [target]
    show sys.make declaration + Multiset.map (fun atom => atom) frame = sys.make declaration + frame
    rw [Multiset.map_id']
  · rintro ⟨frame, source, readable, asked, knowledge, target⟩
    refine ⟨frame, source, readable, asked, True.intro, knowledge, ?_⟩
    rw [target]
    show sys.make declaration + frame = sys.make declaration + Multiset.map (fun atom => atom) frame
    rw [Multiset.map_id']

theorem zoned_run_of_runUnder {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom}
    {uses : List Rule} (run : sys.RunUnder lent k Γ uses k' Γ') :
    ∃ along : (() : Unit) ⟶ (),
      sys.zoned.RunUnder () lent k Γ (uses.map (Sigma.mk ())) () along k' Γ' := by
  induction run with
  | done k Γ => exact ⟨𝟙 (), ZonedSystem.RunUnder.done (sys := sys.zoned) () lent k Γ⟩
  | fire fires later ih =>
      obtain ⟨along, next⟩ := ih
      exact ⟨_, ZonedSystem.RunUnder.fire (sys := sys.zoned) (a := ())
        ((zoned_firesUnder_iff (a := ()) lent _ _ _ _ _).mpr fires)
        (ZonedSystem.RunUnder.relent (sys := sys.zoned) (zoned_carried _ lent).symm next)⟩

theorem runUnder_of_zoned_run {a b : Unit} {lent : Multiset (Const Atom a)} {k : Const K a}
    {Γ : Multiset (Const Atom a)} {uses : List (Sigma (Const Rule))} {along : a ⟶ b}
    {k' : Const K b} {Γ' : Multiset (Const Atom b)}
    (run : sys.zoned.RunUnder a lent k Γ uses b along k' Γ') :
    sys.RunUnder lent k Γ (uses.map fun use => (use.2 : Rule)) k' Γ' := by
  induction run with
  | done a lent k Γ => exact RunUnder.done k Γ
  | fire fires later ih =>
      rw [zoned_carried] at ih
      exact RunUnder.fire ((zoned_firesUnder_iff _ _ _ _ _ _).mp fires) ih

/-- **Runs under a lent context are the one-frame runs of the whole calculus without checks.** -/
theorem runUnder_iff_zoned (lent : Multiset Atom) (k k' : K) (Γ Γ' : Multiset Atom)
    (uses : List Rule) :
    sys.RunUnder lent k Γ uses k' Γ' ↔
      ∃ along : (() : Unit) ⟶ (),
        sys.zoned.RunUnder () lent k Γ (uses.map (Sigma.mk ())) () along k' Γ' := by
  constructor
  · exact zoned_run_of_runUnder
  · rintro ⟨along, run⟩
    have back := runUnder_of_zoned_run run
    rw [map_snd_mk] at back
    exact back

/-- **Runs of the two-zone system are the one-frame runs of the whole calculus without checks
and with nothing lent.** -/
theorem run_iff_zoned (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Run k Γ uses k' Γ' ↔
      ∃ along : (() : Unit) ⟶ (),
        sys.zoned.RunUnder () 0 k Γ (uses.map (Sigma.mk ())) () along k' Γ' :=
  (runUnder_zero_iff_run k k' Γ Γ' uses).symm.trans (runUnder_iff_zoned 0 k k' Γ Γ' uses)

end System

/-! ## One frame, with checks -/

namespace CheckedSystem

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : CheckedSystem K Atom Rule)

/-- One frame. A check of the frame beside the read atoms is a check of every atom the firing
does not take. -/
def zoned : ZonedSystem Unit (Const K) (Const Atom) (Const Rule) where
  know := fun _ k => k
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun _ atom => atom
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a
  extend := fun {a} _ => 𝟙 a
  take := fun declaration => sys.take declaration
  read := fun declaration => sys.read declaration
  make := fun declaration => sys.make declaration
  tell := fun declaration => sys.tell declaration
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro
  check := fun declaration k rest =>
    ∃ frame : Multiset Atom, rest = sys.read declaration + frame ∧ sys.check declaration k frame
  check_mono := fun declaration _ _ _ refines holds =>
    Exists.elim holds fun frame found =>
      ⟨frame, found.1, sys.check_mono declaration frame refines found.2⟩

variable {sys}

theorem zoned_carried {a b : Unit} (step : a ⟶ b) (Γ : Multiset (Const Atom a)) :
    sys.zoned.carried step Γ = Γ :=
  Multiset.map_id' Γ

theorem zoned_firesUnder_zero_iff {a : Unit} (declaration : Const Rule a) (k : Const K a)
    (Γ : Multiset (Const Atom a)) (k' : Const K a) (Γ' : Multiset (Const Atom a)) :
    sys.zoned.FiresUnder 0 declaration k Γ k' Γ' ↔ sys.Fires declaration k Γ k' Γ' := by
  constructor
  · rintro ⟨frame, source, _, _, ⟨rest, split, checked⟩, knowledge, target⟩
    have whole : frame = sys.read declaration + rest := (add_zero frame).symm.trans split
    subst whole
    refine ⟨rest, ?_, checked, knowledge, ?_⟩
    · rw [source]
      show sys.take declaration + (sys.read declaration + rest) =
        sys.take declaration + sys.read declaration + rest
      rw [add_assoc]
    · rw [target]
      show sys.make declaration + Multiset.map (fun atom => atom) (sys.read declaration + rest) =
        sys.read declaration + sys.make declaration + rest
      rw [Multiset.map_id', ← add_assoc, add_comm (sys.make declaration)]
  · rintro ⟨rest, source, checked, knowledge, target⟩
    refine ⟨sys.read declaration + rest, ?_, ?_, True.intro, ⟨rest, add_zero _, checked⟩, knowledge, ?_⟩
    · rw [source]
      show sys.take declaration + sys.read declaration + rest =
        sys.take declaration + (sys.read declaration + rest)
      rw [add_assoc]
    · show sys.read declaration ≤ sys.read declaration + rest + 0
      rw [add_zero]
      exact Multiset.le_add_right _ _
    · rw [target]
      show sys.read declaration + sys.make declaration + rest =
        sys.make declaration + Multiset.map (fun atom => atom) (sys.read declaration + rest)
      rw [Multiset.map_id', ← add_assoc, add_comm (sys.make declaration)]

theorem zoned_run_of_run {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') :
    ∃ along : (() : Unit) ⟶ (),
      sys.zoned.RunUnder () 0 k Γ (uses.map (Sigma.mk ())) () along k' Γ' := by
  induction run with
  | done k Γ => exact ⟨𝟙 (), ZonedSystem.RunUnder.done (sys := sys.zoned) () 0 k Γ⟩
  | fire fires later ih =>
      obtain ⟨along, next⟩ := ih
      exact ⟨_, ZonedSystem.RunUnder.fire (sys := sys.zoned) (a := ())
        ((zoned_firesUnder_zero_iff (a := ()) _ _ _ _ _).mpr fires)
        (ZonedSystem.RunUnder.relent (sys := sys.zoned) (zoned_carried _ 0).symm next)⟩

theorem run_of_zoned_run {a b : Unit} {lent : Multiset (Const Atom a)} {k : Const K a}
    {Γ : Multiset (Const Atom a)} {uses : List (Sigma (Const Rule))} {along : a ⟶ b}
    {k' : Const K b} {Γ' : Multiset (Const Atom b)}
    (run : sys.zoned.RunUnder a lent k Γ uses b along k' Γ') :
    lent = 0 → sys.Run k Γ (uses.map fun use => (use.2 : Rule)) k' Γ' := by
  induction run with
  | done a lent k Γ =>
      intro _
      exact Run.done k Γ
  | fire fires later ih =>
      intro empty
      subst empty
      exact Run.fire ((zoned_firesUnder_zero_iff _ _ _ _ _).mp fires) (ih (zoned_carried _ 0))

/-- **Runs of a checked system are the one-frame runs of the whole calculus with nothing lent.** -/
theorem run_iff_zoned (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Run k Γ uses k' Γ' ↔
      ∃ along : (() : Unit) ⟶ (),
        sys.zoned.RunUnder () 0 k Γ (uses.map (Sigma.mk ())) () along k' Γ' := by
  constructor
  · exact zoned_run_of_run
  · rintro ⟨along, run⟩
    have back := run_of_zoned_run run rfl
    rw [map_snd_mk] at back
    exact back

end CheckedSystem

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
