import Mettapedia.Logic.NormalProgramLoops

/-!
# Propositional normal programs over an arbitrary atom type

The solver-facing kernel of answer set programming. Atoms are elements of an
arbitrary type `A`; in a runtime they are term-store identifiers, not
first-order terms. A rule `head :- pos, not neg` has one head, a list of
positive body atoms and a list of negated body atoms.

## Semantics

* `Program.step P I N` is the immediate-consequence operator with positive
  bodies read in `I` and negation read against `N`. It is monotone in `I` and
  antitone in `N`.
* `Program.Stable P M` (Gelfond–Lifschitz): `M` is the least fixed point of
  `step P · M`, which is the least model of the reduct of `P` by `M`
  (`Program.reduct`, `stable_iff_leastModel_reduct`).
* `Program.Supported P M`: `step P M M = M`, the two-valued models of Clark's
  completion.

## The bridge to the ground-program theory

The ground-program theory (`NormalProgramSemantics`, `ClarkCompletion`,
`NormalProgramLoops`) is stated over the ground atoms of a logic-programming
signature. `atomSignature A` has one nullary relation symbol per atom and no
constants, variables or function symbols, so its ground atoms are equivalent to
`A` (`groundEquiv`). Rules become clauses (`Rule.toClause`) and sets of atoms
become sets of ground atoms (`lift`, an order isomorphism). Under this
translation:

* the immediate-consequence operators agree (`step_lift`), hence so do their
  least fixed points (`lfp_lift`);
* stability, supportedness, positive dependency, tightness, loops and external
  support agree (`stable_iff_stableModel`, `supported_iff_supportedModel`,
  `positiveDependency_embed`, `tight_iff_tight`, `isLoop_map_iff`,
  `externalSupport_map_iff`);
* the existing theorems transfer: stable models are supported
  (`stable_supported`); Fages' theorem for tight programs
  (`stable_iff_supported_of_tight`); every set of true atoms of a stable model
  has external support (`stable_external`); a supported model that is not
  stable contains a true loop without external support (`unsupported_loop`);
  the Lin–Zhao characterization (`stable_iff_supported_loops`); and Clark's
  completion characterizes supported models (`completion_iff_supported`).

No result about stable models is proved twice: each theorem above is the
corresponding ground-program theorem read through the bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open LP BDDCore NormalProgramSemantics ClarkCompletion NormalProgramLoops

universe u

/-- A ground normal rule `head :- pos₁, …, posₘ, not neg₁, …, not negₙ`. -/
structure Rule (A : Type u) where
  head : A
  pos : List A
  neg : List A
  deriving DecidableEq, Repr

/-- A finite ground normal program. Facts are rules with empty bodies. -/
abbrev Program (A : Type u) := List (Rule A)

variable {A : Type u}

namespace Rule

/-- The body holds: every positive atom is in `I` and no negated atom is in `N`. -/
def Holds (r : Rule A) (I N : Set A) : Prop :=
  (∀ b ∈ r.pos, b ∈ I) ∧ ∀ b ∈ r.neg, b ∉ N

theorem Holds.mono {r : Rule A} {I I' N N' : Set A} (h : r.Holds I N) (hI : I ⊆ I') (hN : N' ⊆ N) :
    r.Holds I' N' :=
  ⟨fun b hb => hI (h.1 b hb), fun b hb hb' => h.2 b hb (hN hb')⟩

end Rule

namespace Program

variable (P : Program A)

/-- The immediate-consequence operator: positive bodies read in `I`, negation against `N`. -/
def step (I N : Set A) : Set A := {a | ∃ r ∈ P, r.head = a ∧ r.Holds I N}

theorem step_mono {I I' N N' : Set A} (hI : I ⊆ I') (hN : N' ⊆ N) : P.step I N ⊆ P.step I' N' :=
  fun _ ⟨r, hr, head, body⟩ => ⟨r, hr, head, body.mono hI hN⟩

/-- The operator whose least fixed point is the least model of the reduct by `N`. -/
def reductOp (N : Set A) : Set A →o Set A where
  toFun I := P.step I N
  monotone' _ _ h := P.step_mono h le_rfl

@[simp] theorem reductOp_apply (N I : Set A) : P.reductOp N I = P.step I N := rfl

/-- `N ↦ lfp (step P · N)`, the Gelfond–Lifschitz operator. It is antitone. -/
def glOp (N : Set A) : Set A := (P.reductOp N).lfp

theorem glOp_anti {N N' : Set A} (h : N ⊆ N') : P.glOp N' ⊆ P.glOp N :=
  OrderHom.lfp.monotone fun _ => P.step_mono le_rfl h

/-- **Stable model** (Gelfond–Lifschitz): `M` is the least model of the reduct by `M`. -/
def Stable (M : Set A) : Prop := M = P.glOp M

/-- **Supported model**: every true atom has a rule whose body is true, and conversely. -/
def Supported (M : Set A) : Prop := P.step M M = M

/-- A positive program has no negated body atoms. -/
def IsPositive : Prop := ∀ r ∈ P, r.neg = []

/-- The least model of a program read without negation, the meaning of a positive program. -/
def leastModel : Set A := P.glOp ∅

/-- The atoms that some rule can derive. -/
def headSet : Set A := {a | ∃ r ∈ P, r.head = a}

theorem step_subset_headSet (I N : Set A) : P.step I N ⊆ P.headSet :=
  fun _ ⟨r, hr, head, _⟩ => ⟨r, hr, head⟩

theorem glOp_subset_headSet (N : Set A) : P.glOp N ⊆ P.headSet :=
  OrderHom.lfp_le _ (P.step_subset_headSet _ _)

theorem Stable.subset_headSet {M : Set A} (h : P.Stable M) : M ⊆ P.headSet :=
  h ▸ P.glOp_subset_headSet M

theorem glOp_fixed (N : Set A) : P.step (P.glOp N) N = P.glOp N :=
  (P.reductOp N).map_lfp

/-- Positive dependency, body atom to head: `b` occurs positively in a rule for `a`. -/
def PosDep (b a : A) : Prop := ∃ r ∈ P, r.head = a ∧ b ∈ r.pos

/-- Tightness: positive dependency is well founded (no positive cycles, on a finite program). -/
def Tight : Prop := WellFounded P.PosDep

/-- A rule supports `L` from outside: its head is in `L` and no positive body atom is. -/
def ExternalFor (L : Finset A) (r : Rule A) : Prop := r.head ∈ L ∧ ∀ b ∈ r.pos, b ∉ L

/-- Some rule supports `L` from outside with a body true in `M`. -/
def ExternalSupport (M : Set A) (L : Finset A) : Prop :=
  ∃ r ∈ P, ExternalFor L r ∧ r.Holds M M

/-- The loop formula of `L` holds in `M`: if some atom of `L` is true, `L` has external support. -/
def LoopSatisfied (M : Set A) (L : Finset A) : Prop :=
  (∃ a ∈ L, a ∈ M) → P.ExternalSupport M L

end Program

/-! ## The bridge: one nullary relation symbol per atom -/

/-- The signature with one nullary relation symbol per atom and nothing else. -/
def atomSignature (A : Type u) : LPSignature.{0, 0, u, 0} where
  constants := Empty
  vars := Empty
  relationSymbols := A
  relationArity _ := 0
  functionSymbols := Empty
  functionArity _ := 0

/-- The ground atom of an atom. -/
def embed (a : A) : GroundAtom (atomSignature A) := ⟨a, Fin.elim0⟩

/-- Ground atoms of `atomSignature A` are the atoms. -/
def groundEquiv : GroundAtom (atomSignature A) ≃ A where
  toFun g := g.symbol
  invFun := embed
  left_inv g := by
    obtain ⟨symbol, args⟩ := g
    change (⟨symbol, Fin.elim0⟩ : GroundAtom (atomSignature A)) = ⟨symbol, args⟩
    congr
    funext i
    exact (show Fin 0 from i).elim0
  right_inv _ := rfl

@[simp] theorem groundEquiv_embed (a : A) : groundEquiv (embed a) = a := rfl
@[simp] theorem groundEquiv_symm (a : A) : groundEquiv.symm a = embed a := rfl
@[simp] theorem embed_groundEquiv (g : GroundAtom (atomSignature A)) : embed (groundEquiv g) = g :=
  groundEquiv.left_inv g

theorem embed_injective : Function.Injective (embed : A → GroundAtom (atomSignature A)) :=
  groundEquiv.symm.injective

@[simp] theorem embed_inj {a b : A} : embed a = embed b ↔ a = b := embed_injective.eq_iff

instance [DecidableEq A] : DecidableEq (GroundAtom (atomSignature A)) := groundEquiv.decidableEq

/-- A rule as a ground normal clause: positive literals first, then negated ones. -/
def Rule.toClause (r : Rule A) : NormalClause (atomSignature A) where
  head := embed r.head
  body := r.pos.map (GoalLit.pos ∘ embed) ++ r.neg.map (GoalLit.neg ∘ embed)

/-- A program as a list of ground normal clauses. -/
def Program.clauses (P : Program A) : List (NormalClause (atomSignature A)) := P.map Rule.toClause

/-- A set of atoms as a set of ground atoms. -/
def lift (S : Set A) : Set (GroundAtom (atomSignature A)) := groundEquiv ⁻¹' S

/-- A set of ground atoms as a set of atoms. -/
def unlift (T : Set (GroundAtom (atomSignature A))) : Set A := groundEquiv.symm ⁻¹' T

@[simp] theorem mem_lift {S : Set A} {g : GroundAtom (atomSignature A)} : g ∈ lift S ↔ groundEquiv g ∈ S :=
  Iff.rfl

@[simp] theorem embed_mem_lift {S : Set A} {a : A} : embed a ∈ lift S ↔ a ∈ S := Iff.rfl

@[simp] theorem lift_unlift (T : Set (GroundAtom (atomSignature A))) : lift (unlift T) = T :=
  groundEquiv.preimage_symm_preimage T

@[simp] theorem unlift_lift (S : Set A) : unlift (lift S) = S := groundEquiv.symm_preimage_preimage S

theorem lift_subset_lift {S S' : Set A} : lift S ⊆ lift S' ↔ S ⊆ S' :=
  ⟨fun h _ ha => h (embed_mem_lift.mpr ha), fun h _ hg => h hg⟩

theorem lift_injective : Function.Injective (lift : Set A → Set (GroundAtom (atomSignature A))) :=
  fun S S' h => by rw [← unlift_lift S, h, unlift_lift]

@[simp] theorem lift_inj {S S' : Set A} : lift S = lift S' ↔ S = S' := lift_injective.eq_iff

@[simp] theorem positiveBody_toClause (r : Rule A) : positiveBody r.toClause = r.pos.map embed := by
  obtain ⟨head, pos, neg⟩ := r
  induction pos with
  | nil => simp [positiveBody, Rule.toClause]
  | cons a pos ih => simp [positiveBody, Rule.toClause] at ih ⊢

theorem pos_mem_toClause (r : Rule A) (g : GroundAtom (atomSignature A)) :
    GoalLit.pos g ∈ r.toClause.body ↔ groundEquiv g ∈ r.pos := by
  rw [← mem_positiveBody, positiveBody_toClause, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨groundEquiv g, h, embed_groundEquiv g⟩

theorem neg_mem_toClause (r : Rule A) (g : GroundAtom (atomSignature A)) :
    GoalLit.neg g ∈ r.toClause.body ↔ groundEquiv g ∈ r.neg := by
  simp only [Rule.toClause, List.mem_append, List.mem_map, Function.comp_apply, reduceCtorEq,
    and_false, exists_false, GoalLit.neg.injEq, false_or]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨groundEquiv g, h, embed_groundEquiv g⟩

theorem bodyHolds_toClause (r : Rule A) (I N : Set A) :
    normalClauseBodyHolds r.toClause (lift I) (lift N) ↔ r.Holds I N := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · exact h (.pos (embed b)) ((pos_mem_toClause r _).mpr hb)
    · exact h (.neg (embed b)) ((neg_mem_toClause r _).mpr hb)
  · rintro ⟨hp, hn⟩ g hg
    cases g with
    | pos g => exact hp _ ((pos_mem_toClause r g).mp hg)
    | neg g => exact hn _ ((neg_mem_toClause r g).mp hg)
    | neq x y =>
      simp [Rule.toClause] at hg

theorem bodyHolds_toClause' (r : Rule A) (I N : Set (GroundAtom (atomSignature A))) :
    normalClauseBodyHolds r.toClause I N ↔ r.Holds (unlift I) (unlift N) := by
  rw [← bodyHolds_toClause, lift_unlift, lift_unlift]

namespace Program

variable (P : Program A)

theorem step_lift (I N : Set A) : T_normal P.clauses (lift I) (lift N) = lift (P.step I N) := by
  ext g
  simp only [T_normal, Program.clauses, List.mem_map, Set.mem_ofPred_eq, mem_lift, step]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, head, body⟩
    refine ⟨r, hr, ?_, (bodyHolds_toClause r I N).mp body⟩
    rw [← head]
    rfl
  · rintro ⟨r, hr, head, body⟩
    refine ⟨r.toClause, ⟨r, hr, rfl⟩, ?_, (bodyHolds_toClause r I N).mpr body⟩
    change embed r.head = g
    rw [head, embed_groundEquiv]

theorem orderHom_lift (N I : Set A) :
    T_normal_orderHom P.clauses ∅ (lift N) (lift I) = lift (P.reductOp N I) := by
  change ∅ ∪ T_normal P.clauses (lift I) (lift N) = _
  rw [Set.empty_union, step_lift]
  rfl

/-- The least fixed points agree under the bridge. -/
theorem lfp_lift (N : Set A) : (T_normal_orderHom P.clauses ∅ (lift N)).lfp = lift (P.glOp N) := by
  apply le_antisymm
  · apply OrderHom.lfp_le_fixed
    rw [orderHom_lift, glOp, OrderHom.map_lfp]
  · rw [← lift_unlift (T_normal_orderHom P.clauses ∅ (lift N)).lfp, lift_subset_lift]
    apply OrderHom.lfp_le
    rw [← lift_subset_lift, ← orderHom_lift, lift_unlift, OrderHom.map_lfp]

theorem stable_iff_stableModel (M : Set A) : P.Stable M ↔ StableModel P.clauses ∅ (lift M) := by
  rw [stable_iff, lfp_lift, lift_inj]
  rfl

theorem supported_iff_supportedModel (M : Set A) :
    P.Supported M ↔ SupportedModel P.clauses ∅ (lift M) := by
  rw [SupportedModel, Set.empty_union, step_lift, lift_inj]
  rfl

theorem positiveDependency_embed (b a : A) :
    PositiveDependency P.clauses (embed b) (embed a) ↔ P.PosDep b a := by
  simp only [PositiveDependency, Program.clauses, List.mem_map]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, head, body⟩
    exact ⟨r, hr, embed_injective head, (pos_mem_toClause r _).mp body⟩
  · rintro ⟨r, hr, rfl, body⟩
    exact ⟨r.toClause, ⟨r, hr, rfl⟩, rfl, (pos_mem_toClause r (embed b)).mpr body⟩

theorem positiveDependency_iff (g h : GroundAtom (atomSignature A)) :
    PositiveDependency P.clauses g h ↔ P.PosDep (groundEquiv g) (groundEquiv h) := by
  rw [← positiveDependency_embed, embed_groundEquiv, embed_groundEquiv]

theorem tight_iff_tight : NormalProgramSemantics.Tight P.clauses ↔ P.Tight := by
  have relation : PositiveDependency P.clauses = InvImage P.PosDep groundEquiv := by
    funext g h
    exact propext (positiveDependency_iff P g h)
  have back : P.PosDep = InvImage (PositiveDependency P.clauses) (groundEquiv.symm) := by
    funext b a
    exact propext (positiveDependency_embed P b a).symm
  constructor
  · intro tight
    unfold Program.Tight
    rw [back]
    exact InvImage.wf _ tight
  · intro tight
    rw [NormalProgramSemantics.Tight, relation]
    exact InvImage.wf _ tight

/-! ### Transferred theorems -/

/-- Stable models are supported. -/
theorem stable_supported {M : Set A} (h : P.Stable M) : P.Supported M :=
  (P.supported_iff_supportedModel M).mpr
    (NormalProgramSemantics.stable_supported ((P.stable_iff_stableModel M).mp h))

/-- **Fages' theorem**: on a tight program, stable and supported models coincide. -/
theorem stable_iff_supported_of_tight (tight : P.Tight) (M : Set A) : P.Stable M ↔ P.Supported M := by
  rw [stable_iff_stableModel, supported_iff_supportedModel]
  exact NormalProgramSemantics.stable_iff_supported ((P.tight_iff_tight).mpr tight) ∅ (lift M)

end Program

/-! ### Loops and external support through the bridge -/

section Loops

variable [DecidableEq A]

/-- Finite sets of atoms as finite sets of ground atoms. -/
def liftFinset (L : Finset A) : Finset (GroundAtom (atomSignature A)) :=
  L.map groundEquiv.symm.toEmbedding

@[simp] theorem mem_liftFinset {L : Finset A} {g : GroundAtom (atomSignature A)} :
    g ∈ liftFinset L ↔ groundEquiv g ∈ L := by
  simp only [liftFinset, Finset.mem_map_equiv, Equiv.symm_symm]

theorem embed_mem_liftFinset {L : Finset A} {a : A} : embed a ∈ liftFinset L ↔ a ∈ L := by
  simp

omit [DecidableEq A] in
theorem liftFinset_surjective (L' : Finset (GroundAtom (atomSignature A))) :
    liftFinset (L'.map groundEquiv.toEmbedding) = L' := by
  ext g
  simp [liftFinset]

/-- Loops are invariant under a relation-preserving equivalence of atom types. -/
theorem FiniteLoops.isLoop_map_equiv {B : Type*} [DecidableEq B] (e : A ≃ B)
    (R : A → A → Prop) (S : B → B → Prop) (preserves : ∀ a b, S (e a) (e b) ↔ R a b) (L : Finset A) :
    FiniteLoops.IsLoop S (L.map e.toEmbedding) ↔ FiniteLoops.IsLoop R L := by
  have forward : ∀ a b, Relation.TransGen (FiniteLoops.inside R L) a b →
      Relation.TransGen (FiniteLoops.inside S (L.map e.toEmbedding)) (e a) (e b) := by
    intro a b path
    refine Relation.TransGen.lift e (fun x y edge => ?_) _ _ path
    exact ⟨Finset.mem_map_of_mem _ edge.1, Finset.mem_map_of_mem _ edge.2.1, (preserves x y).mpr edge.2.2⟩
  have backward : ∀ x y, Relation.TransGen (FiniteLoops.inside S (L.map e.toEmbedding)) x y →
      Relation.TransGen (FiniteLoops.inside R L) (e.symm x) (e.symm y) := by
    intro x y path
    refine Relation.TransGen.lift e.symm (fun x y edge => ?_) _ _ path
    obtain ⟨hx, hy, rel⟩ := edge
    rw [Finset.mem_map_equiv] at hx hy
    refine ⟨hx, hy, ?_⟩
    rw [← preserves, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact rel
  constructor
  · rintro ⟨nonempty, connected⟩
    refine ⟨?_, fun a ha b hb => ?_⟩
    · obtain ⟨x, hx⟩ := nonempty
      rw [Finset.mem_map_equiv] at hx
      exact ⟨_, hx⟩
    · have := backward _ _ (connected (e a) (Finset.mem_map_of_mem _ ha) (e b) (Finset.mem_map_of_mem _ hb))
      simpa using this
  · rintro ⟨nonempty, connected⟩
    refine ⟨nonempty.map, fun x hx y hy => ?_⟩
    rw [Finset.mem_map_equiv] at hx hy
    have := forward _ _ (connected _ hx _ hy)
    simpa using this

namespace Program

variable (P : Program A)

/-- A loop: a nonempty set of atoms strongly connected by positive dependency inside it. -/
def IsLoop (L : Finset A) : Prop := FiniteLoops.IsLoop P.PosDep L

/-- A tight program has no loops. -/
theorem not_isLoop_of_tight (tight : P.Tight) (L : Finset A) : ¬ P.IsLoop L := by
  rintro ⟨⟨a, ha⟩, connected⟩
  have path : Relation.TransGen P.PosDep a a :=
    Relation.TransGen.mono (fun _ _ (edge : FiniteLoops.inside P.PosDep L _ _) => edge.2.2) a a
      (connected a ha a ha)
  exact tight.transGen.irrefl.irrefl a path

theorem isLoop_map_iff (L : Finset A) : NormalProgramLoops.IsLoop P.clauses (liftFinset L) ↔ P.IsLoop L :=
  FiniteLoops.isLoop_map_equiv groundEquiv.symm P.PosDep (PositiveDependency P.clauses)
    (fun b a => P.positiveDependency_embed b a) L

theorem externalSupport_map_iff (M : Set A) (L : Finset A) :
    NormalProgramLoops.ExternalSupport P.clauses ∅ (lift M) (liftFinset L) ↔ P.ExternalSupport M L := by
  simp only [NormalProgramLoops.ExternalSupport, Set.mem_empty_iff_false, and_false, exists_false,
    false_or, Program.clauses, List.mem_map, NormalProgramLoops.ExternalRule]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, ⟨head, outside⟩, body⟩
    refine ⟨r, hr, ⟨embed_mem_liftFinset.mp head, fun b hb inL => ?_⟩, (bodyHolds_toClause r M M).mp body⟩
    apply outside (embed b) _ (embed_mem_liftFinset.mpr inL)
    rw [positiveBody_toClause]
    exact List.mem_map_of_mem hb
  · rintro ⟨r, hr, ⟨head, outside⟩, body⟩
    refine ⟨r.toClause, ⟨r, hr, rfl⟩, ⟨embed_mem_liftFinset.mpr head, fun g hg inL => ?_⟩,
      (bodyHolds_toClause r M M).mpr body⟩
    rw [positiveBody_toClause, List.mem_map] at hg
    obtain ⟨b, hb, rfl⟩ := hg
    exact outside b hb (embed_mem_liftFinset.mp inL)

theorem loopSatisfied_map_iff (M : Set A) (L : Finset A) :
    NormalProgramLoops.LoopSatisfied P.clauses ∅ (lift M) (liftFinset L) ↔ P.LoopSatisfied M L := by
  simp only [NormalProgramLoops.LoopSatisfied, Program.LoopSatisfied, externalSupport_map_iff]
  apply imp_congr_left
  constructor
  · rintro ⟨g, hg, hM⟩
    exact ⟨groundEquiv g, mem_liftFinset.mp hg, hM⟩
  · rintro ⟨a, ha, hM⟩
    exact ⟨embed a, embed_mem_liftFinset.mpr ha, hM⟩

/-- Every set of atoms with a true member in a stable model has external support. -/
theorem stable_external {M : Set A} (h : P.Stable M) (L : Finset A) : P.LoopSatisfied M L :=
  (P.loopSatisfied_map_iff M L).mp
    (NormalProgramLoops.stable_external ((P.stable_iff_stableModel M).mp h) (liftFinset L))

/-- **The loop witness.** A supported model that is not stable contains a loop of true atoms
without external support. This is what a solver's unfounded-set check finds. -/
theorem unsupported_loop {M : Set A} (supported : P.Supported M) (notStable : ¬ P.Stable M) :
    ∃ L : Finset A, ↑L ⊆ M ∧ P.IsLoop L ∧ ¬ P.ExternalSupport M L := by
  obtain ⟨L', subset, loop, unsupported⟩ := NormalProgramLoops.unsupported_loop
    ((P.supported_iff_supportedModel M).mp supported) (mt (P.stable_iff_stableModel M).mpr notStable)
  refine ⟨L'.map groundEquiv.toEmbedding, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    exact subset hg
  · rw [← isLoop_map_iff, liftFinset_surjective]
    exact loop
  · rw [← externalSupport_map_iff, liftFinset_surjective]
    exact unsupported

/-- **Lin–Zhao**: stable models are the supported models satisfying every loop formula. -/
theorem stable_iff_supported_loops (M : Set A) :
    P.Stable M ↔ P.Supported M ∧ ∀ L, P.IsLoop L → P.LoopSatisfied M L := by
  constructor
  · intro h
    exact ⟨P.stable_supported h, fun L _ => P.stable_external h L⟩
  · rintro ⟨supported, loops⟩
    by_contra notStable
    obtain ⟨L, subset, loop, unsupported⟩ := P.unsupported_loop supported notStable
    obtain ⟨a, ha⟩ := loop.1
    exact unsupported (loops L loop ⟨a, ha, subset ha⟩)

/-! ### Clark's completion -/

/-- The atom table of the completion: every atom of the program, in order of occurrence. -/
def completionTable : AtomTable (GroundAtom (atomSignature A)) := programTable (n := 0) Fin.elim0 P.clauses []

omit [DecidableEq A] in
theorem chosenFacts_empty (choice : Fin 0 → Bool) :
    chosenFacts (σ := atomSignature A) Fin.elim0 choice = ∅ := by
  ext g
  simp only [chosenFacts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, _⟩
  exact i.elim0

/-- **Clark's completion** characterizes supported models: a valuation of the program's atom
table satisfies the completion formula exactly when the atoms it makes true form a supported
model. -/
theorem completion_iff_supported (values : Fin P.completionTable.atoms.length → Bool) :
    PropositionalTseitin.eval (Fin.addCases Fin.elim0 values) (completion P.completionTable Fin.elim0 P.clauses) = true ↔
      P.Supported (unlift (P.completionTable.interpretation values)) := by
  rw [completion_models P.completionTable Fin.elim0 P.clauses (programTable_covers _ _ _), chosenFacts_empty, supported_iff_supportedModel,
    lift_unlift]

end Program

end Loops

end Mettapedia.Logic.ASP
