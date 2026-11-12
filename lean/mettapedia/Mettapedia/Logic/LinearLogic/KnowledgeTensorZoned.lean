import Mathlib.Data.Multiset.Filter
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrames

/-!
# The whole calculus: knowledge, lent atoms, owned atoms, checks, over frames

One declaration takes owned atoms, reads lent or framed atoms, makes atoms, tells knowledge and
fires under a guard on knowledge and a check. It fires along its frame map, which transports
knowledge, the frame and the lent context into its target frame, where names may be born. The
check reads the knowledge after the tell and every present atom the firing does not take.

A proof is over a frame map, has a lent zone and an owned zone, and carries a grade: the extra
contexts it admits. A leaf admits the contexts its check accepts; `widen` lends more and shifts
the grade; `lend` turns owned atoms into lent ones for a sub-proof; `strengthen` adds knowledge;
`cut` composes and conjoins the grades, the later one transported back along the frame map.

## Results

* `Proves.run`: a proof runs under every extra context its grade admits.
* `run_iff_proves`: a run under a lent context exists exactly when a proof exists whose grade
  admits the empty extra context, with the same leaves over the same frame map.

The two-zone tensor logic, its lent zone, the frame grades and the frame-indexed proofs are
fragments of this calculus: one frame without checks, one frame with checks, or frames without
checks. `KnowledgeTensorFragments` proves that their runs are runs of this calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

open _root_.CategoryTheory

universe uF uH uK uAtom uRule

/-- Declared transitions over frames whose check reads the atoms the firing does not take. -/
structure ZonedSystem (Frame : Type uF) [Category.{uH} Frame] (K : Frame → Type uK)
    [∀ a, SemilatticeInf (K a)] (Atom : Frame → Type uAtom) (Rule : Frame → Type uRule)
    extends IndexedSystem Frame K Atom Rule where
  check : ∀ {a : Frame} (declaration : Rule a), K (target declaration) → Multiset (Atom a) → Prop
  check_mono : ∀ {a : Frame} (declaration : Rule a) {stronger weaker : K (target declaration)}
    (rest : Multiset (Atom a)), stronger ≤ weaker → check declaration weaker rest →
      check declaration stronger rest

namespace ZonedSystem

open IndexedSystem

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule} (sys : ZonedSystem Frame K Atom Rule)

/-- One firing under a lent context. The frame is carried along; the check reads the frame and
the lent context. -/
abbrev FiresUnder {a : Frame} (lent : Multiset (Atom a)) (declaration : Rule a) (k : K a)
    (Γ : Multiset (Atom a)) (k' : K (sys.target declaration))
    (Γ' : Multiset (Atom (sys.target declaration))) : Prop :=
  ∃ frame : Multiset (Atom a), Γ = sys.take declaration + frame ∧
    sys.read declaration ≤ frame + lent ∧
    sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) ∧
    sys.check declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (frame + lent) ∧
    k' = sys.know (sys.extend declaration) k ⊓ sys.tell declaration ∧
    Γ' = sys.make declaration + sys.carried (sys.extend declaration) frame

/-- A run under a lent context, over a frame map. The lent context is carried along. -/
inductive RunUnder : (a : Frame) → Multiset (Atom a) → K a → Multiset (Atom a) → List (Sigma Rule) →
    (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) → Prop
  | done (a : Frame) (lent : Multiset (Atom a)) (k : K a) (Γ : Multiset (Atom a)) :
      RunUnder a lent k Γ [] a (𝟙 a) k Γ
  | fire {a b : Frame} {lent : Multiset (Atom a)} {declaration : Rule a} {k : K a}
      {Γ : Multiset (Atom a)} {k₁ : K (sys.target declaration)}
      {Γ₁ : Multiset (Atom (sys.target declaration))} {rest : List (Sigma Rule)}
      {along : sys.target declaration ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} :
      sys.FiresUnder lent declaration k Γ k₁ Γ₁ →
      RunUnder (sys.target declaration) (sys.carried (sys.extend declaration) lent) k₁ Γ₁ rest b along
        k' Γ' →
        RunUnder a lent k Γ (⟨a, declaration⟩ :: rest) b (sys.extend declaration ≫ along) k' Γ'

/-- Graded proofs with a lent zone, over a frame map. -/
inductive Proves : (a : Frame) → Multiset (Atom a) → K a → Multiset (Atom a) →
    (Multiset (Atom a) → Prop) → List (Sigma Rule) → (b : Frame) → (a ⟶ b) → K b →
    Multiset (Atom b) → Prop
  | identity (a : Frame) (lent : Multiset (Atom a)) (k : K a) (Γ : Multiset (Atom a)) :
      Proves a lent k Γ (fun _ => True) [] a (𝟙 a) k Γ
  | rule {a : Frame} (declaration : Rule a) (k : K a)
      (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
      Proves a (sys.read declaration) k (sys.take declaration)
        (fun extra => sys.check declaration
          (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.read declaration + extra))
        [⟨a, declaration⟩] (sys.target declaration) (sys.extend declaration)
        (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.make declaration)
  | widen {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
      {grade : Multiset (Atom a) → Prop} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)} (more : Multiset (Atom a)) :
      Proves a lent k Γ grade uses b along k' Γ' →
        Proves a (lent + more) k Γ (fun extra => grade (more + extra)) uses b along k' Γ'
  | lend {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
      {grade : Multiset (Atom a) → Prop} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)} (borrowed : Multiset (Atom a)) :
      Proves a (lent + borrowed) k Γ grade uses b along k' Γ' →
        Proves a lent k (Γ + borrowed) grade uses b along k' (Γ' + sys.carried along borrowed)
  | strengthen {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
      {grade : Multiset (Atom a) → Prop} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)} (more : K a) :
      Proves a lent k Γ grade uses b along k' Γ' →
        Proves a lent (k ⊓ more) Γ grade uses b along (k' ⊓ sys.know along more) Γ'
  | cut {a b c : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
      {early : Multiset (Atom a) → Prop} {first second : List (Sigma Rule)} {along : a ⟶ b}
      {k₁ : K b} {Γ₁ : Multiset (Atom b)} {late : Multiset (Atom b) → Prop} {onward : b ⟶ c}
      {k' : K c} {Γ' : Multiset (Atom c)} :
      Proves a lent k Γ early first b along k₁ Γ₁ →
      Proves b (sys.carried along lent) k₁ Γ₁ late second c onward k' Γ' →
        Proves a lent k Γ (fun extra => early extra ∧ late (sys.carried along extra))
          (first ++ second) c (along ≫ onward) k' Γ'
  | restrict {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
      {grade stricter : Multiset (Atom a) → Prop} {uses : List (Sigma Rule)} {along : a ⟶ b}
      {k' : K b} {Γ' : Multiset (Atom b)} (implies : ∀ extra, stricter extra → grade extra) :
      Proves a lent k Γ grade uses b along k' Γ' → Proves a lent k Γ stricter uses b along k' Γ'

variable {sys}

/-! ## Laws of firings and runs -/

theorem FiresUnder.lend {a : Frame} {lent : Multiset (Atom a)} (borrowed : Multiset (Atom a))
    {declaration : Rule a} {k : K a} {Γ : Multiset (Atom a)} {k' : K (sys.target declaration)}
    {Γ' : Multiset (Atom (sys.target declaration))}
    (fires : sys.FiresUnder (lent + borrowed) declaration k Γ k' Γ') :
    sys.FiresUnder lent declaration k (Γ + borrowed) k'
      (Γ' + sys.carried (sys.extend declaration) borrowed) := by
  obtain ⟨frame, source, readable, asked, checked, knowledge, target⟩ := fires
  have regrouped : frame + borrowed + lent = frame + (lent + borrowed) := by
    rw [add_assoc, add_comm borrowed lent]
  refine ⟨frame + borrowed, by rw [source, add_assoc], ?_, asked, ?_, knowledge,
    by rw [target, carried_add, add_assoc]⟩
  · rw [regrouped]
    exact readable
  · rw [regrouped]
    exact checked

theorem FiresUnder.strengthen {a : Frame} {lent : Multiset (Atom a)} (more : K a)
    {declaration : Rule a} {k : K a} {Γ : Multiset (Atom a)} {k' : K (sys.target declaration)}
    {Γ' : Multiset (Atom (sys.target declaration))}
    (fires : sys.FiresUnder lent declaration k Γ k' Γ') :
    sys.FiresUnder lent declaration (k ⊓ more) Γ (k' ⊓ sys.know (sys.extend declaration) more) Γ' := by
  obtain ⟨frame, source, readable, asked, checked, knowledge, target⟩ := fires
  have below : sys.know (sys.extend declaration) (k ⊓ more) ⊓ sys.tell declaration ≤
      sys.know (sys.extend declaration) k ⊓ sys.tell declaration := by
    rw [sys.know_inf]
    exact inf_le_inf_right _ inf_le_left
  refine ⟨frame, source, readable, sys.guard_mono declaration below asked,
    sys.check_mono declaration _ below checked, ?_, target⟩
  rw [knowledge, sys.know_inf, inf_right_comm]

theorem RunUnder.append {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
    {k₁ : K b} {Γ₁ : Multiset (Atom b)} {first : List (Sigma Rule)} {along : a ⟶ b}
    (one : sys.RunUnder a lent k Γ first b along k₁ Γ₁) :
    ∀ {c : Frame} {k' : K c} {Γ' : Multiset (Atom c)} {second : List (Sigma Rule)} {onward : b ⟶ c},
      sys.RunUnder b (sys.carried along lent) k₁ Γ₁ second c onward k' Γ' →
        sys.RunUnder a lent k Γ (first ++ second) c (along ≫ onward) k' Γ' := by
  induction one with
  | done a lent k Γ =>
      intro c k' Γ' second onward two
      rw [carried_id] at two
      rw [Category.id_comp]
      exact two
  | fire fires later ih =>
      intro c k' Γ' second onward two
      rw [carried_comp] at two
      rw [Category.assoc]
      exact RunUnder.fire fires (ih two)

/-- Lending: atoms lent to a run may instead be owned beside it, and are returned carried. -/
theorem RunUnder.lend {a b : Frame} {whole : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
    {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (run : sys.RunUnder a whole k Γ uses b along k' Γ') :
    ∀ lent borrowed : Multiset (Atom a), whole = lent + borrowed →
      sys.RunUnder a lent k (Γ + borrowed) uses b along k' (Γ' + sys.carried along borrowed) := by
  induction run with
  | done a whole k Γ =>
      intro lent borrowed _
      rw [carried_id]
      exact RunUnder.done a lent k (Γ + borrowed)
  | fire fires later ih =>
      intro lent borrowed same
      subst same
      rw [carried_comp]
      exact RunUnder.fire (FiresUnder.lend borrowed fires) (ih _ _ (carried_add _ lent borrowed))

theorem RunUnder.strengthen {a b : Frame} {lent : Multiset (Atom a)} {k : K a}
    {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (run : sys.RunUnder a lent k Γ uses b along k' Γ') :
    ∀ more : K a, sys.RunUnder a lent (k ⊓ more) Γ uses b along (k' ⊓ sys.know along more) Γ' := by
  induction run with
  | done a lent k Γ =>
      intro more
      rw [sys.know_id]
      exact RunUnder.done a lent (k ⊓ more) Γ
  | fire fires later ih =>
      intro more
      rw [sys.know_comp]
      exact RunUnder.fire (FiresUnder.strengthen more fires) (ih _)

/-! ## Runs and graded proofs -/

/-- **The frame law relative to the grade.** A proof runs under every extra context its grade
admits. -/
theorem Proves.run {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
    {grade : Multiset (Atom a) → Prop} {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (proof : sys.Proves a lent k Γ grade uses b along k' Γ') :
    ∀ extra : Multiset (Atom a), grade extra →
      sys.RunUnder a (lent + extra) k Γ uses b along k' Γ' := by
  induction proof with
  | identity a lent k Γ =>
      intro extra _
      exact RunUnder.done a (lent + extra) k Γ
  | @rule a declaration k asked =>
      intro extra checked
      have checkedHere : sys.check declaration
          (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)
          (0 + (sys.read declaration + extra)) := by
        rw [zero_add]
        exact checked
      have fires : sys.FiresUnder (sys.read declaration + extra) declaration k (sys.take declaration)
          (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.make declaration) :=
        ⟨0, (add_zero _).symm,
          le_of_le_of_eq (Multiset.le_add_right _ _) (zero_add _).symm, asked, checkedHere, rfl,
          by rw [carried_zero, add_zero]⟩
      have run := RunUnder.fire fires (RunUnder.done _ _ _ _)
      rw [Category.comp_id] at run
      exact run
  | widen more prior ih =>
      intro extra graded
      simpa only [add_assoc] using ih (more + extra) graded
  | @lend a b lent k Γ grade uses along k' Γ' borrowed prior ih =>
      intro extra graded
      exact RunUnder.lend (ih extra graded) (lent + extra) borrowed (add_right_comm lent borrowed extra)
  | strengthen more prior ih =>
      intro extra graded
      exact RunUnder.strengthen (ih extra graded) more
  | cut first second ihFirst ihSecond =>
      intro extra graded
      have late := ihSecond _ graded.2
      rw [← carried_add] at late
      exact RunUnder.append (ihFirst extra graded.1) late
  | restrict implies prior ih =>
      intro extra graded
      exact ih extra (implies extra graded)

/-- A run under a lent context is a proof whose grade admits the empty extra context. -/
theorem RunUnder.proves {a b : Frame} {lent : Multiset (Atom a)} {k : K a} {Γ : Multiset (Atom a)}
    {uses : List (Sigma Rule)} {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (run : sys.RunUnder a lent k Γ uses b along k' Γ') :
    ∃ grade : Multiset (Atom a) → Prop, grade 0 ∧ sys.Proves a lent k Γ grade uses b along k' Γ' := by
  induction run with
  | done a lent k Γ => exact ⟨fun _ => True, trivial, Proves.identity a lent k Γ⟩
  | @fire a b lent declaration k Γ k₁ Γ₁ rest along k' Γ' fires later ih =>
      obtain ⟨frame, source, readable, asked, checked, knowledge, target⟩ := fires
      obtain ⟨late, lateAtZero, proof⟩ := ih
      obtain ⟨more, split⟩ := Multiset.le_iff_exists_add.mp readable
      subst source knowledge target
      have zone : sys.read declaration + more = lent + frame := by
        rw [← split, add_comm]
      have leaf := Proves.widen more (Proves.rule declaration k asked)
      rw [zone] at leaf
      refine ⟨fun extra => sys.check declaration
          (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)
          (sys.read declaration + (more + extra)) ∧ late (sys.carried (sys.extend declaration) extra),
        ⟨?_, ?_⟩, Proves.cut (Proves.lend frame leaf) proof⟩
      · rw [add_zero, ← split]
        exact checked
      · rw [carried_zero]
        exact lateAtZero

/-- **Runs correspond to graded proofs, in the whole calculus.** -/
theorem run_iff_proves {a b : Frame} (lent : Multiset (Atom a)) (k : K a) (Γ : Multiset (Atom a))
    (uses : List (Sigma Rule)) (along : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)) :
    sys.RunUnder a lent k Γ uses b along k' Γ' ↔
      ∃ grade : Multiset (Atom a) → Prop, grade 0 ∧
        sys.Proves a lent k Γ grade uses b along k' Γ' := by
  constructor
  · exact RunUnder.proves
  · rintro ⟨grade, atZero, proof⟩
    simpa only [add_zero] using Proves.run proof 0 atZero

end ZonedSystem

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
