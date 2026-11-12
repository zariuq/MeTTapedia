import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Multiset.MapFold
import Mettapedia.Logic.LinearLogic.KnowledgeTensor

/-!
# Tensor proofs over knowledge indexed by frames

Frames form a category. Each frame has its own knowledge semilattice and its own atoms, and a
frame map transports both: knowledge by a meet-preserving map (`know`), atoms by a function
(`carry`), functorially. A declaration at a frame fires along its own frame map (`extend`) into
its target frame. It takes and reads atoms of the source frame; what it read and the whole
residual frame are carried along; it makes atoms of the target frame, and it tells and is guarded
in the target frame, over the transported knowledge.

Names born at a firing are the atoms and the knowledge of the target frame that are not
transported from the source (`Fresh`).

A proof lies over a frame map, the composite of the maps of its leaves. The two frame rules
transport along it: `frame` carries the extra atoms, `strengthen` carries the extra knowledge.

## Results

* `derives_iff_run`: a proof with a given list of leaves over a given frame map exists exactly
  when the run with that word over that map exists.
* `Derives.refines`: the final knowledge refines the transported initial knowledge.
* `Fresh.not_carried`: an atom made fresh is none of the atoms carried along.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

open _root_.CategoryTheory

universe uF uH uK uAtom uRule

/-- Declared transitions over knowledge and atoms indexed by a category of frames. -/
structure IndexedSystem (Frame : Type uF) [Category.{uH} Frame] (K : Frame → Type uK)
    [∀ a, SemilatticeInf (K a)] (Atom : Frame → Type uAtom) (Rule : Frame → Type uRule) where
  know : ∀ {a b : Frame}, (a ⟶ b) → K a → K b
  know_id : ∀ {a : Frame} (k : K a), know (𝟙 a) k = k
  know_comp : ∀ {a b c : Frame} (f : a ⟶ b) (g : b ⟶ c) (k : K a), know (f ≫ g) k = know g (know f k)
  know_inf : ∀ {a b : Frame} (f : a ⟶ b) (k more : K a), know f (k ⊓ more) = know f k ⊓ know f more
  carry : ∀ {a b : Frame}, (a ⟶ b) → Atom a → Atom b
  carry_id : ∀ {a : Frame} (atom : Atom a), carry (𝟙 a) atom = atom
  carry_comp : ∀ {a b c : Frame} (f : a ⟶ b) (g : b ⟶ c) (atom : Atom a),
    carry (f ≫ g) atom = carry g (carry f atom)
  target : ∀ {a : Frame}, Rule a → Frame
  extend : ∀ {a : Frame} (declaration : Rule a), a ⟶ target declaration
  take : ∀ {a : Frame}, Rule a → Multiset (Atom a)
  read : ∀ {a : Frame}, Rule a → Multiset (Atom a)
  make : ∀ {a : Frame} (declaration : Rule a), Multiset (Atom (target declaration))
  tell : ∀ {a : Frame} (declaration : Rule a), K (target declaration)
  guard : ∀ {a : Frame} (declaration : Rule a), K (target declaration) → Prop
  guard_mono : ∀ {a : Frame} (declaration : Rule a) {stronger weaker : K (target declaration)},
    stronger ≤ weaker → guard declaration weaker → guard declaration stronger

namespace IndexedSystem

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule} (sys : IndexedSystem Frame K Atom Rule)

/-- Atoms carried along a frame map. -/
def carried {a b : Frame} (f : a ⟶ b) (Γ : Multiset (Atom a)) : Multiset (Atom b) :=
  Γ.map (sys.carry f)

def premises {a : Frame} (declaration : Rule a) : Multiset (Atom a) :=
  sys.take declaration + sys.read declaration

/-- What a use leaves in its target frame: what it read, carried along, and what it makes. -/
def conclusions {a : Frame} (declaration : Rule a) : Multiset (Atom (sys.target declaration)) :=
  sys.carried (sys.extend declaration) (sys.read declaration) + sys.make declaration

/-- One firing along the declaration's frame map, over its complete residual frame. -/
abbrev Fires {a : Frame} (declaration : Rule a) (k : K a) (Γ : Multiset (Atom a))
    (k' : K (sys.target declaration)) (Γ' : Multiset (Atom (sys.target declaration))) : Prop :=
  ∃ frame : Multiset (Atom a), Γ = sys.premises declaration + frame ∧
    sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) ∧
    k' = sys.know (sys.extend declaration) k ⊓ sys.tell declaration ∧
    Γ' = sys.conclusions declaration + sys.carried (sys.extend declaration) frame

/-- A run over a frame map. -/
inductive Run : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) →
    (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) → Prop
  | done (a : Frame) (k : K a) (Γ : Multiset (Atom a)) : Run a k Γ [] a (𝟙 a) k Γ
  | fire {a b : Frame} {declaration : Rule a} {k : K a} {Γ : Multiset (Atom a)}
      {k₁ : K (sys.target declaration)} {Γ₁ : Multiset (Atom (sys.target declaration))}
      {rest : List (Sigma Rule)} {along : sys.target declaration ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)} :
      sys.Fires declaration k Γ k₁ Γ₁ → Run (sys.target declaration) k₁ Γ₁ rest b along k' Γ' →
        Run a k Γ (⟨a, declaration⟩ :: rest) b (sys.extend declaration ≫ along) k' Γ'

/-- Proofs over a frame map. -/
inductive Derives : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) →
    (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) → Prop
  | identity (a : Frame) (k : K a) (Γ : Multiset (Atom a)) : Derives a k Γ [] a (𝟙 a) k Γ
  | rule {a : Frame} (declaration : Rule a) (k : K a)
      (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
      Derives a k (sys.premises declaration) [⟨a, declaration⟩] (sys.target declaration)
        (sys.extend declaration) (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)
        (sys.conclusions declaration)
  | frame {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)} {along : a ⟶ b}
      {k' : K b} {Γ' : Multiset (Atom b)} (extra : Multiset (Atom a)) :
      Derives a k Γ uses b along k' Γ' →
        Derives a k (Γ + extra) uses b along k' (Γ' + sys.carried along extra)
  | strengthen {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
      {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (more : K a) :
      Derives a k Γ uses b along k' Γ' →
        Derives a (k ⊓ more) Γ uses b along (k' ⊓ sys.know along more) Γ'
  | cut {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {first second : List (Sigma Rule)}
      {along : a ⟶ b} {k₁ : K b} {Γ₁ : Multiset (Atom b)} {onward : b ⟶ c} {k' : K c}
      {Γ' : Multiset (Atom c)} :
      Derives a k Γ first b along k₁ Γ₁ → Derives b k₁ Γ₁ second c onward k' Γ' →
        Derives a k Γ (first ++ second) c (along ≫ onward) k' Γ'

/-- Every atom a declaration makes is new: none is carried from its source frame. -/
def Fresh {a : Frame} (declaration : Rule a) : Prop :=
  ∀ atom ∈ sys.make declaration, ∀ old : Atom a, sys.carry (sys.extend declaration) old ≠ atom

variable {sys}

/-! ## Transport -/

theorem carried_zero {a b : Frame} (f : a ⟶ b) : sys.carried f (0 : Multiset (Atom a)) = 0 :=
  Multiset.map_zero _

theorem carried_add {a b : Frame} (f : a ⟶ b) (Γ Δ : Multiset (Atom a)) :
    sys.carried f (Γ + Δ) = sys.carried f Γ + sys.carried f Δ :=
  Multiset.map_add _ _ _

theorem carried_id {a : Frame} (Γ : Multiset (Atom a)) : sys.carried (𝟙 a) Γ = Γ := by
  unfold carried
  rw [show sys.carry (𝟙 a) = id from funext sys.carry_id]
  exact Multiset.map_id Γ

theorem carried_comp {a b c : Frame} (f : a ⟶ b) (g : b ⟶ c) (Γ : Multiset (Atom a)) :
    sys.carried (f ≫ g) Γ = sys.carried g (sys.carried f Γ) := by
  unfold carried
  rw [Multiset.map_map]
  exact congrArg (fun step => Multiset.map step Γ) (funext (sys.carry_comp f g))

theorem know_mono {a b : Frame} (f : a ⟶ b) {stronger weaker : K a} (refines : stronger ≤ weaker) :
    sys.know f stronger ≤ sys.know f weaker := by
  have joined := sys.know_inf f stronger weaker
  rw [inf_eq_left.mpr refines] at joined
  rw [joined]
  exact inf_le_right

/-- An atom made fresh is none of the atoms carried along. -/
theorem Fresh.not_carried {a : Frame} {declaration : Rule a} (fresh : sys.Fresh declaration)
    {atom : Atom (sys.target declaration)} (made : atom ∈ sys.make declaration)
    (old : Multiset (Atom a)) : atom ∉ sys.carried (sys.extend declaration) old := by
  intro member
  obtain ⟨source, _, same⟩ := Multiset.mem_map.mp member
  exact fresh atom made source same

/-! ## Laws of firings and runs -/

theorem Fires.frame {a : Frame} {declaration : Rule a} {k : K a} {Γ : Multiset (Atom a)}
    {k' : K (sys.target declaration)} {Γ' : Multiset (Atom (sys.target declaration))}
    (extra : Multiset (Atom a)) (fires : sys.Fires declaration k Γ k' Γ') :
    sys.Fires declaration k (Γ + extra) k' (Γ' + sys.carried (sys.extend declaration) extra) := by
  obtain ⟨frame, source, asked, knowledge, target⟩ := fires
  exact ⟨frame + extra, by rw [source, add_assoc], asked, knowledge,
    by rw [target, carried_add, add_assoc]⟩

theorem Fires.strengthen {a : Frame} {declaration : Rule a} {k : K a} {Γ : Multiset (Atom a)}
    {k' : K (sys.target declaration)} {Γ' : Multiset (Atom (sys.target declaration))}
    (more : K a) (fires : sys.Fires declaration k Γ k' Γ') :
    sys.Fires declaration (k ⊓ more) Γ (k' ⊓ sys.know (sys.extend declaration) more) Γ' := by
  obtain ⟨frame, source, asked, knowledge, target⟩ := fires
  refine ⟨frame, source, ?_, ?_, target⟩
  · rw [sys.know_inf]
    exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked
  · rw [knowledge, sys.know_inf, inf_right_comm]

theorem Run.append {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {first : List (Sigma Rule)} {along : a ⟶ b}
    (one : sys.Run a k Γ first b along k₁ Γ₁) :
    ∀ {c : Frame} {k' : K c} {Γ' : Multiset (Atom c)} {second : List (Sigma Rule)} {onward : b ⟶ c},
      sys.Run b k₁ Γ₁ second c onward k' Γ' →
        sys.Run a k Γ (first ++ second) c (along ≫ onward) k' Γ' := by
  induction one with
  | done a k Γ =>
      intro c k' Γ' second onward two
      rw [Category.id_comp]
      exact two
  | fire fires later ih =>
      intro c k' Γ' second onward two
      rw [Category.assoc]
      exact Run.fire fires (ih two)

/-- The frame law of runs: extra atoms are carried along the run's frame map. -/
theorem Run.frame {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (run : sys.Run a k Γ uses b along k' Γ') :
    ∀ extra : Multiset (Atom a),
      sys.Run a k (Γ + extra) uses b along k' (Γ' + sys.carried along extra) := by
  induction run with
  | done a k Γ =>
      intro extra
      rw [carried_id]
      exact Run.done a k (Γ + extra)
  | fire fires later ih =>
      intro extra
      rw [carried_comp]
      exact Run.fire (Fires.frame extra fires) (ih _)

/-- The frame law of knowledge: extra knowledge is transported along the run's frame map. -/
theorem Run.strengthen {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (run : sys.Run a k Γ uses b along k' Γ') :
    ∀ more : K a, sys.Run a (k ⊓ more) Γ uses b along (k' ⊓ sys.know along more) Γ' := by
  induction run with
  | done a k Γ =>
      intro more
      rw [sys.know_id]
      exact Run.done a (k ⊓ more) Γ
  | fire fires later ih =>
      intro more
      rw [sys.know_comp]
      exact Run.fire (Fires.strengthen more fires) (ih _)

/-- The final knowledge refines the initial knowledge, transported along the run. -/
theorem Run.refines {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (run : sys.Run a k Γ uses b along k' Γ') :
    k' ≤ sys.know along k := by
  induction run with
  | done a k Γ => exact le_of_eq (sys.know_id k).symm
  | fire fires later ih =>
      obtain ⟨_, _, _, knowledge, _⟩ := fires
      rw [sys.know_comp]
      refine ih.trans (know_mono _ ?_)
      rw [knowledge]
      exact inf_le_left

/-! ## Runs and proofs -/

/-- **Completeness.** A proof over a frame map is a run with the same word over the same map. -/
theorem Derives.run {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (proof : sys.Derives a k Γ uses b along k' Γ') : sys.Run a k Γ uses b along k' Γ' := by
  induction proof with
  | identity a k Γ => exact Run.done a k Γ
  | @rule a declaration k asked =>
      have fires : sys.Fires declaration k (sys.premises declaration)
          (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.conclusions declaration) :=
        ⟨0, (add_zero _).symm, asked, rfl, by rw [carried_zero, add_zero]⟩
      have run := Run.fire fires (Run.done _ _ _)
      rw [Category.comp_id] at run
      exact run
  | frame extra prior ih => exact Run.frame ih extra
  | strengthen more prior ih => exact Run.strengthen ih more
  | cut first second ihFirst ihSecond => exact Run.append ihFirst ihSecond

/-- **Soundness.** A run over a frame map is a proof with the same word over the same map. -/
theorem Run.derives {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (run : sys.Run a k Γ uses b along k' Γ') : sys.Derives a k Γ uses b along k' Γ' := by
  induction run with
  | done a k Γ => exact Derives.identity a k Γ
  | fire fires later ih =>
      obtain ⟨frame, source, asked, knowledge, target⟩ := fires
      subst source knowledge target
      exact Derives.cut (Derives.frame frame (Derives.rule _ _ asked)) ih

/-- **Runs correspond to proofs over frames**, with the same leaves over the same frame map. -/
theorem derives_iff_run {a b : Frame} (k : K a) (Γ : Multiset (Atom a)) (uses : List (Sigma Rule))
    (along : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)) :
    sys.Derives a k Γ uses b along k' Γ' ↔ sys.Run a k Γ uses b along k' Γ' :=
  ⟨Derives.run, Run.derives⟩

/-- The final knowledge of a proof refines its initial knowledge, transported along the proof. -/
theorem Derives.refines {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (proof : sys.Derives a k Γ uses b along k' Γ') : k' ≤ sys.know along k :=
  Run.refines (Derives.run proof)

end IndexedSystem

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
