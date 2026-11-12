import Mettapedia.Logic.LinearLogic.KnowledgeTensor

/-!
# Three zones: knowledge, lent atoms and owned atoms

A sequent has three zones. Knowledge is persistent and only refines. Owned atoms are linear.
Lent atoms are present for the whole proof, are read and never taken, and are shared by the
parts of a proof that run side by side.

A leaf owns what its declaration takes and is lent what it reads. `lend` turns owned atoms into
lent ones for a sub-proof and returns them afterwards; `grow` lends more than is needed. The
frame rule for owned atoms is derived (`Lends.frame`): a frame is lent and never read.

## Results

* `lends_iff_runUnder`: a proof exists exactly when the run under the lent context exists.
* `runUnder_zero_iff_run`, `lends_iff_derives`: with nothing lent, these are the runs and the
  proofs of the two-zone calculus, where a read is a returned premise.
* `Lends.tensor`, `Lends.tensor_swap`: parallel composition shares the lent context.
* `shared_read_diamond`: two uses whose reads are served by one shared context, and whose guards
  hold without the other's tell, run in both orders to the same state. The shared context is not
  duplicated: one occurrence serves both reads. The two-zone tensor needs a copy for each.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

namespace System

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- One firing under a lent context: a read is served by the frame or by what is lent. -/
abbrev FiresUnder (lent : Multiset Atom) (declaration : Rule) (k : K) (Γ : Multiset Atom) (k' : K)
    (Γ' : Multiset Atom) : Prop :=
  ∃ frame : Multiset Atom, Γ = sys.take declaration + frame ∧
    sys.read declaration ≤ frame + lent ∧ sys.guard declaration (k ⊓ sys.tell declaration) ∧
    k' = k ⊓ sys.tell declaration ∧ Γ' = sys.make declaration + frame

/-- A run under a lent context, which no firing takes. -/
inductive RunUnder (lent : Multiset Atom) : K → Multiset Atom → List Rule → K → Multiset Atom → Prop
  | done (k : K) (Γ : Multiset Atom) : RunUnder lent k Γ [] k Γ
  | fire {declaration : Rule} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {rest : List Rule} :
      sys.FiresUnder lent declaration k Γ k₁ Γ₁ → RunUnder lent k₁ Γ₁ rest k' Γ' →
        RunUnder lent k Γ (declaration :: rest) k' Γ'

/-- Proofs with a lent zone. -/
inductive Lends : Multiset Atom → K → Multiset Atom → List Rule → K → Multiset Atom → Prop
  | identity (lent : Multiset Atom) (k : K) (Γ : Multiset Atom) : Lends lent k Γ [] k Γ
  | rule (declaration : Rule) (k : K) (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
      Lends (sys.read declaration) k (sys.take declaration) [declaration]
        (k ⊓ sys.tell declaration) (sys.make declaration)
  | grow {lent wider : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
      (within : lent ≤ wider) : Lends lent k Γ uses k' Γ' → Lends wider k Γ uses k' Γ'
  | lend {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
      (borrowed : Multiset Atom) :
      Lends (lent + borrowed) k Γ uses k' Γ' → Lends lent k (Γ + borrowed) uses k' (Γ' + borrowed)
  | strengthen {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (more : K) :
      Lends lent k Γ uses k' Γ' → Lends lent (k ⊓ more) Γ uses (k' ⊓ more) Γ'
  | cut {lent : Multiset Atom} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {first second : List Rule} :
      Lends lent k Γ first k₁ Γ₁ → Lends lent k₁ Γ₁ second k' Γ' →
        Lends lent k Γ (first ++ second) k' Γ'

variable {sys}

/-! ## Laws of firings and runs under a lent context -/

theorem FiresUnder.grow {lent wider : Multiset Atom} (within : lent ≤ wider) {declaration : Rule}
    {k k' : K} {Γ Γ' : Multiset Atom} (fires : sys.FiresUnder lent declaration k Γ k' Γ') :
    sys.FiresUnder wider declaration k Γ k' Γ' := by
  obtain ⟨frame, source, readable, asked, knowledge, target⟩ := fires
  exact ⟨frame, source, readable.trans (Multiset.add_le_add_left within), asked, knowledge, target⟩

theorem FiresUnder.lend {lent : Multiset Atom} (borrowed : Multiset Atom) {declaration : Rule}
    {k k' : K} {Γ Γ' : Multiset Atom}
    (fires : sys.FiresUnder (lent + borrowed) declaration k Γ k' Γ') :
    sys.FiresUnder lent declaration k (Γ + borrowed) k' (Γ' + borrowed) := by
  obtain ⟨frame, source, readable, asked, knowledge, target⟩ := fires
  have regrouped : frame + borrowed + lent = frame + (lent + borrowed) := by
    rw [add_assoc, add_comm borrowed lent]
  refine ⟨frame + borrowed, by rw [source, add_assoc], ?_, asked, knowledge, by rw [target, add_assoc]⟩
  rw [regrouped]
  exact readable

theorem FiresUnder.strengthen {lent : Multiset Atom} (more : K) {declaration : Rule} {k k' : K}
    {Γ Γ' : Multiset Atom} (fires : sys.FiresUnder lent declaration k Γ k' Γ') :
    sys.FiresUnder lent declaration (k ⊓ more) Γ (k' ⊓ more) Γ' := by
  obtain ⟨frame, source, readable, asked, knowledge, target⟩ := fires
  refine ⟨frame, source, readable, sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked,
    ?_, target⟩
  rw [knowledge, inf_right_comm]

theorem FiresUnder.refines {lent : Multiset Atom} {declaration : Rule} {k k' : K}
    {Γ Γ' : Multiset Atom} (fires : sys.FiresUnder lent declaration k Γ k' Γ') : k' ≤ k := by
  obtain ⟨_, _, _, _, knowledge, _⟩ := fires
  rw [knowledge]
  exact inf_le_left

/-- A firing under a lent context is a function of its declaration and its source. -/
theorem FiresUnder.deterministic {lent : Multiset Atom} {declaration : Rule} {k k₁ k₂ : K}
    {Γ Γ₁ Γ₂ : Multiset Atom} (one : sys.FiresUnder lent declaration k Γ k₁ Γ₁)
    (two : sys.FiresUnder lent declaration k Γ k₂ Γ₂) : k₁ = k₂ ∧ Γ₁ = Γ₂ := by
  obtain ⟨frame, source, _, _, knowledge, target⟩ := one
  obtain ⟨other, source', _, _, knowledge', target'⟩ := two
  have same : frame = other := add_left_cancel (source.symm.trans source')
  exact ⟨knowledge.trans knowledge'.symm, by rw [target, target', same]⟩

theorem RunUnder.append {lent : Multiset Atom} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom}
    {first second : List Rule} (one : sys.RunUnder lent k Γ first k₁ Γ₁)
    (two : sys.RunUnder lent k₁ Γ₁ second k' Γ') : sys.RunUnder lent k Γ (first ++ second) k' Γ' := by
  induction one with
  | done k Γ => exact two
  | fire fires later ih => exact RunUnder.fire fires (ih two)

theorem RunUnder.grow {lent wider : Multiset Atom} (within : lent ≤ wider) {k k' : K}
    {Γ Γ' : Multiset Atom} {uses : List Rule} (run : sys.RunUnder lent k Γ uses k' Γ') :
    sys.RunUnder wider k Γ uses k' Γ' := by
  induction run with
  | done k Γ => exact RunUnder.done k Γ
  | fire fires later ih => exact RunUnder.fire (FiresUnder.grow within fires) ih

theorem RunUnder.lend {lent : Multiset Atom} (borrowed : Multiset Atom) {k k' : K}
    {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.RunUnder (lent + borrowed) k Γ uses k' Γ') :
    sys.RunUnder lent k (Γ + borrowed) uses k' (Γ' + borrowed) := by
  induction run with
  | done k Γ => exact RunUnder.done k (Γ + borrowed)
  | fire fires later ih => exact RunUnder.fire (FiresUnder.lend borrowed fires) ih

theorem RunUnder.strengthen {lent : Multiset Atom} (more : K) {k k' : K} {Γ Γ' : Multiset Atom}
    {uses : List Rule} (run : sys.RunUnder lent k Γ uses k' Γ') :
    sys.RunUnder lent (k ⊓ more) Γ uses (k' ⊓ more) Γ' := by
  induction run with
  | done k Γ => exact RunUnder.done (k ⊓ more) Γ
  | fire fires later ih => exact RunUnder.fire (FiresUnder.strengthen more fires) ih

theorem RunUnder.refines {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.RunUnder lent k Γ uses k' Γ') : k' ≤ k := by
  induction run with
  | done k Γ => exact le_rfl
  | fire fires later ih => exact ih.trans (FiresUnder.refines fires)

/-! ## Runs and proofs -/

/-- **Completeness.** A proof with a lent zone is a run under the lent context. -/
theorem Lends.run {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Lends lent k Γ uses k' Γ') : sys.RunUnder lent k Γ uses k' Γ' := by
  induction proof with
  | identity lent k Γ => exact RunUnder.done k Γ
  | rule declaration k asked =>
      have fires : sys.FiresUnder (sys.read declaration) declaration k (sys.take declaration)
          (k ⊓ sys.tell declaration) (sys.make declaration) :=
        ⟨0, (add_zero _).symm, le_of_eq (zero_add _).symm, asked, rfl, (add_zero _).symm⟩
      exact RunUnder.fire fires (RunUnder.done _ _)
  | grow within prior ih => exact RunUnder.grow within ih
  | lend borrowed prior ih => exact RunUnder.lend borrowed ih
  | strengthen more prior ih => exact RunUnder.strengthen more ih
  | cut first second ihFirst ihSecond => exact RunUnder.append ihFirst ihSecond

/-- **Soundness.** A run under a lent context is a proof with that lent zone. -/
theorem RunUnder.lends {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.RunUnder lent k Γ uses k' Γ') : sys.Lends lent k Γ uses k' Γ' := by
  induction run with
  | done k Γ => exact Lends.identity lent k Γ
  | @fire declaration k k₁ k' Γ Γ₁ Γ' rest fires later ih =>
      obtain ⟨frame, source, readable, asked, knowledge, target⟩ := fires
      subst source knowledge target
      have within : sys.read declaration ≤ lent + frame := by
        rw [add_comm]
        exact readable
      exact Lends.cut (Lends.lend frame (Lends.grow within (Lends.rule declaration k asked))) ih

/-- **Runs under a lent context correspond to proofs with a lent zone.** -/
theorem lends_iff_runUnder (lent : Multiset Atom) (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Lends lent k Γ uses k' Γ' ↔ sys.RunUnder lent k Γ uses k' Γ' :=
  ⟨Lends.run, RunUnder.lends⟩

theorem firesUnder_zero_iff_fires (declaration : Rule) (k k' : K) (Γ Γ' : Multiset Atom) :
    sys.FiresUnder 0 declaration k Γ k' Γ' ↔ sys.Fires declaration k Γ k' Γ' := by
  constructor
  · rintro ⟨frame, source, readable, asked, knowledge, target⟩
    rw [add_zero] at readable
    obtain ⟨rest, split⟩ := Multiset.le_iff_exists_add.mp readable
    subst split
    refine ⟨rest, ?_, asked, knowledge, ?_⟩
    · rw [source, premises, add_assoc]
    · rw [target, conclusions, ← add_assoc, add_comm (sys.make declaration) (sys.read declaration)]
  · rintro ⟨rest, source, asked, knowledge, target⟩
    refine ⟨sys.read declaration + rest, ?_, ?_, asked, knowledge, ?_⟩
    · rw [source, premises, add_assoc]
    · rw [add_zero]
      exact Multiset.le_add_right _ _
    · rw [target, conclusions, ← add_assoc, add_comm (sys.make declaration) (sys.read declaration)]

/-- With nothing lent, a run under the lent context is a run. -/
theorem runUnder_zero_iff_run (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.RunUnder 0 k Γ uses k' Γ' ↔ sys.Run k Γ uses k' Γ' := by
  constructor
  · intro run
    induction run with
    | done k Γ => exact Run.done k Γ
    | fire fires later ih => exact Run.fire ((firesUnder_zero_iff_fires _ _ _ _ _).mp fires) ih
  · intro run
    induction run with
    | done k Γ => exact RunUnder.done k Γ
    | fire fires later ih => exact RunUnder.fire ((firesUnder_zero_iff_fires _ _ _ _ _).mpr fires) ih

/-- With nothing lent, the three-zone proofs are the two-zone proofs. -/
theorem lends_iff_derives (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Lends 0 k Γ uses k' Γ' ↔ sys.Derives k Γ uses k' Γ' :=
  (lends_iff_runUnder 0 k k' Γ Γ' uses).trans
    ((runUnder_zero_iff_run k k' Γ Γ' uses).trans (derives_iff_run k k' Γ Γ' uses).symm)

/-! ## Derived rules -/

theorem Lends.refines {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Lends lent k Γ uses k' Γ') : k' ≤ k :=
  RunUnder.refines (Lends.run proof)

/-- The frame rule for owned atoms: a frame is lent and never read. -/
theorem Lends.frame {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (extra : Multiset Atom) (proof : sys.Lends lent k Γ uses k' Γ') :
    sys.Lends lent k (Γ + extra) uses k' (Γ' + extra) :=
  Lends.lend extra (Lends.grow (Multiset.le_add_right lent extra) proof)

/-- Parallel composition over one shared lent context, read left then right. -/
theorem Lends.tensor {lent : Multiset Atom} {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom}
    {first second : List Rule} (one : sys.Lends lent k Γ first k₁ Γ')
    (two : sys.Lends lent k Δ second k₂ Δ') :
    sys.Lends lent k (Γ + Δ) (first ++ second) (k₁ ⊓ k₂) (Γ' + Δ') := by
  have later := Lends.frame Γ' (Lends.strengthen k₁ two)
  rw [inf_eq_right.mpr (Lends.refines one), add_comm Δ Γ', add_comm Δ' Γ', inf_comm k₂ k₁] at later
  exact Lends.cut (Lends.frame Δ one) later

/-- The same parallel composition read right then left. -/
theorem Lends.tensor_swap {lent : Multiset Atom} {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom}
    {first second : List Rule} (one : sys.Lends lent k Γ first k₁ Γ')
    (two : sys.Lends lent k Δ second k₂ Δ') :
    sys.Lends lent k (Γ + Δ) (second ++ first) (k₁ ⊓ k₂) (Γ' + Δ') := by
  have swapped := Lends.tensor two one
  rw [add_comm Δ Γ, add_comm Δ' Γ', inf_comm k₂ k₁] at swapped
  exact swapped

/-- A proof with a lent zone is a run that owns the lent atoms and returns them. -/
theorem Lends.run_owning {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Lends lent k Γ uses k' Γ') : sys.Run k (Γ + lent) uses k' (Γ' + lent) := by
  have whole : sys.Lends (0 + lent) k Γ uses k' Γ' := by
    rw [zero_add]
    exact proof
  exact (runUnder_zero_iff_run _ _ _ _ _).mp (Lends.run (Lends.lend lent whole))

/-- **The diamond of shared reads.** Two uses whose reads are served by one shared context, and
whose guards hold without the other's tell, run in both orders from the same state to the same
state. The shared context is one copy for both. -/
theorem shared_read_diamond (first second : Rule) (k : K) (shared : Multiset Atom)
    (firstReads : sys.read first ≤ shared) (secondReads : sys.read second ≤ shared)
    (firstAsked : sys.guard first (k ⊓ sys.tell first))
    (secondAsked : sys.guard second (k ⊓ sys.tell second)) :
    sys.Run k (sys.take first + sys.take second + shared) [first, second]
        (k ⊓ sys.tell first ⊓ (k ⊓ sys.tell second)) (sys.make first + sys.make second + shared) ∧
      sys.Run k (sys.take first + sys.take second + shared) [second, first]
        (k ⊓ sys.tell first ⊓ (k ⊓ sys.tell second)) (sys.make first + sys.make second + shared) := by
  have one := Lends.grow firstReads (Lends.rule first k firstAsked)
  have two := Lends.grow secondReads (Lends.rule second k secondAsked)
  exact ⟨Lends.run_owning (Lends.tensor one two), Lends.run_owning (Lends.tensor_swap one two)⟩

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
