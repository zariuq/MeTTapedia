import Mathlib.Order.Lattice
import Mettapedia.Logic.LinearLogic.TensorHornEquivalence

/-!
# Tensor proofs over a knowledge zone

A state has two zones. The linear zone is a multiset of atoms. The knowledge zone is one element
of a meet semilattice, ordered by refinement: `stronger ≤ weaker`. Knowledge is persistent, so it
is neither counted nor consumed, and telling is the meet.

A declared transition takes atoms, reads atoms and returns them, makes atoms, tells knowledge and
fires under a guard. The guard is asked of the knowledge after the tell and is stable under
refinement (`guard_mono`). A read atom is a premise that is returned, so one occurrence serves one
read position of a firing and survives it.

`Derives` is the proof calculus: identity, one leaf per use of a declaration, a frame rule for
each zone (`frame` for atoms, `strengthen` for knowledge) and cut. There is no weakening and no
contraction of atoms, and the conclusion keeps the complete residual boundary of both zones. The
proof calculus mentions no run.

## Results

* `derives_iff_run`: a proof with a given list of leaves exists exactly when the run with that
  word exists. The direction from proofs to runs is a sequential normal form.
* `Derives.tensor`, `Derives.tensor_swap`: parallel composition is derived, in both orders, with
  the joined knowledge.
* `Derives.refines`: knowledge only refines along a proof.
* `Derives.fibre`: a proof supplies a multiplicative Horn derivation, hence a tensor sequent
  (`Derives.tensor_sequent`), all of whose leaves are admitted at the final knowledge.
* `run_iff_horn_of_stationary`: for runs that learn nothing, Horn derivations over the
  declarations admitted at the fixed knowledge are exact. With learning the converse fails,
  because a guard may be asked before the knowledge it needs is told; the controls file has the
  separating example.
* `Derives.preserves_valuation`: every additive invariant of the declarations is an invariant of
  proofs, so no atom is discarded or invented.
* `derivesUpTo_iff_run`, `DerivesUpTo.cut`: a conclusion may forget knowledge. Such a proof
  exists exactly when a run reaches knowledge at least as strong, and these proofs compose.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

/-- Declared transitions over a knowledge semilattice. -/
structure System (K : Type uK) (Atom : Type uAtom) (Rule : Type uRule) [SemilatticeInf K] where
  take : Rule → Multiset Atom
  read : Rule → Multiset Atom
  make : Rule → Multiset Atom
  tell : Rule → K
  guard : Rule → K → Prop
  guard_mono : ∀ (declaration : Rule) {stronger weaker : K},
    stronger ≤ weaker → guard declaration weaker → guard declaration stronger

namespace System

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- The atoms a use needs: what it takes and what it reads. -/
def premises (declaration : Rule) : Multiset Atom := sys.take declaration + sys.read declaration

/-- The atoms a use leaves: what it read and what it makes. -/
def conclusions (declaration : Rule) : Multiset Atom := sys.read declaration + sys.make declaration

/-- One firing, over its complete residual frame. -/
abbrev Fires (declaration : Rule) (k : K) (Γ : Multiset Atom) (k' : K) (Γ' : Multiset Atom) : Prop :=
  ∃ frame : Multiset Atom, Γ = sys.premises declaration + frame ∧
    sys.guard declaration (k ⊓ sys.tell declaration) ∧ k' = k ⊓ sys.tell declaration ∧
    Γ' = sys.conclusions declaration + frame

/-- A run: a word of declarations, each fired where its predecessors left the state. -/
inductive Run : K → Multiset Atom → List Rule → K → Multiset Atom → Prop
  | done (k : K) (Γ : Multiset Atom) : Run k Γ [] k Γ
  | fire {declaration : Rule} {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {rest : List Rule} :
      sys.Fires declaration k Γ k₁ Γ₁ → Run k₁ Γ₁ rest k' Γ' → Run k Γ (declaration :: rest) k' Γ'

/-- Proofs. The list is the left-to-right readout of the declaration leaves. -/
inductive Derives : K → Multiset Atom → List Rule → K → Multiset Atom → Prop
  | identity (k : K) (Γ : Multiset Atom) : Derives k Γ [] k Γ
  | rule (declaration : Rule) (k : K) (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
      Derives k (sys.premises declaration) [declaration] (k ⊓ sys.tell declaration)
        (sys.conclusions declaration)
  | frame {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (extra : Multiset Atom) :
      Derives k Γ uses k' Γ' → Derives k (Γ + extra) uses k' (Γ' + extra)
  | strengthen {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (more : K) :
      Derives k Γ uses k' Γ' → Derives (k ⊓ more) Γ uses (k' ⊓ more) Γ'
  | cut {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} {first second : List Rule} :
      Derives k Γ first k₁ Γ₁ → Derives k₁ Γ₁ second k' Γ' → Derives k Γ (first ++ second) k' Γ'

/-- A declaration is admitted at a knowledge that already holds its tell and passes its guard. -/
structure AdmittedAt (k : K) (declaration : Rule) : Prop where
  told : k ≤ sys.tell declaration
  asked : sys.guard declaration k

variable {sys}

/-! ## Laws of firings and runs -/

theorem Fires.frame {declaration : Rule} {k k' : K} {Γ Γ' : Multiset Atom} (extra : Multiset Atom)
    (fires : sys.Fires declaration k Γ k' Γ') :
    sys.Fires declaration k (Γ + extra) k' (Γ' + extra) := by
  obtain ⟨frame, source, asked, knowledge, target⟩ := fires
  exact ⟨frame + extra, by rw [source, add_assoc], asked, knowledge, by rw [target, add_assoc]⟩

theorem Fires.strengthen {declaration : Rule} {k k' : K} {Γ Γ' : Multiset Atom} (more : K)
    (fires : sys.Fires declaration k Γ k' Γ') :
    sys.Fires declaration (k ⊓ more) Γ (k' ⊓ more) Γ' := by
  obtain ⟨frame, source, asked, knowledge, target⟩ := fires
  refine ⟨frame, source, sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked, ?_, target⟩
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

/-- The frame law of runs in the linear zone. -/
theorem Run.frame {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (extra : Multiset Atom)
    (run : sys.Run k Γ uses k' Γ') : sys.Run k (Γ + extra) uses k' (Γ' + extra) := by
  induction run with
  | done k Γ => exact Run.done k (Γ + extra)
  | fire fires later ih => exact Run.fire (Fires.frame extra fires) ih

/-- The frame law of runs in the knowledge zone: more knowledge disables nothing. -/
theorem Run.strengthen {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (more : K)
    (run : sys.Run k Γ uses k' Γ') : sys.Run (k ⊓ more) Γ uses (k' ⊓ more) Γ' := by
  induction run with
  | done k Γ => exact Run.done (k ⊓ more) Γ
  | fire fires later ih => exact Run.fire (Fires.strengthen more fires) ih

theorem Run.refines {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') : k' ≤ k := by
  induction run with
  | done k Γ => exact le_rfl
  | fire fires later ih => exact ih.trans (Fires.refines fires)

/-! ## Runs and proofs -/

/-- **Completeness.** A proof is a run with the same word: frames and strengthenings are pushed to
the leaves, and cuts become concatenation. -/
theorem Derives.run {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') : sys.Run k Γ uses k' Γ' := by
  induction proof with
  | identity k Γ => exact Run.done k Γ
  | rule declaration k asked =>
      have fires : sys.Fires declaration k (sys.premises declaration) (k ⊓ sys.tell declaration)
          (sys.conclusions declaration) := ⟨0, (add_zero _).symm, asked, rfl, (add_zero _).symm⟩
      exact Run.fire fires (Run.done _ _)
  | frame extra prior ih => exact Run.frame extra ih
  | strengthen more prior ih => exact Run.strengthen more ih
  | cut first second ihFirst ihSecond => exact Run.append ihFirst ihSecond

/-- **Soundness.** A run is a proof with the same word, over the complete residual boundary. -/
theorem Run.derives {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') : sys.Derives k Γ uses k' Γ' := by
  induction run with
  | done k Γ => exact Derives.identity k Γ
  | fire fires later ih =>
      obtain ⟨frame, source, asked, knowledge, target⟩ := fires
      subst source knowledge target
      exact Derives.cut (Derives.frame frame (Derives.rule _ _ asked)) ih

/-- **Runs correspond to proofs**, with the same leaves in the same order. -/
theorem derives_iff_run (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Derives k Γ uses k' Γ' ↔ sys.Run k Γ uses k' Γ' :=
  ⟨Derives.run, Run.derives⟩

/-- Knowledge only refines along a proof. -/
theorem Derives.refines {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') : k' ≤ k :=
  Run.refines (Derives.run proof)

/-- Parallel composition, read left then right. Both proofs start from the same knowledge and
the result holds the knowledge of both. -/
theorem Derives.tensor {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom} {first second : List Rule}
    (one : sys.Derives k Γ first k₁ Γ') (two : sys.Derives k Δ second k₂ Δ') :
    sys.Derives k (Γ + Δ) (first ++ second) (k₁ ⊓ k₂) (Γ' + Δ') := by
  have later := Derives.frame Γ' (Derives.strengthen k₁ two)
  rw [inf_eq_right.mpr (Derives.refines one), add_comm Δ Γ', add_comm Δ' Γ', inf_comm k₂ k₁] at later
  exact Derives.cut (Derives.frame Δ one) later

/-- The same parallel composition read right then left: independent proofs run in either order
to the same state. -/
theorem Derives.tensor_swap {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom} {first second : List Rule}
    (one : sys.Derives k Γ first k₁ Γ') (two : sys.Derives k Δ second k₂ Δ') :
    sys.Derives k (Γ + Δ) (second ++ first) (k₁ ⊓ k₂) (Γ' + Δ') := by
  have swapped := Derives.tensor two one
  rw [add_comm Δ Γ, add_comm Δ' Γ', inf_comm k₂ k₁] at swapped
  exact swapped

/-! ## The fibre over the final knowledge -/

/-- Every leaf of a proof is admitted at the final knowledge. -/
theorem Derives.admitted {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') : ∀ declaration ∈ uses, sys.AdmittedAt k' declaration := by
  induction proof with
  | identity k Γ =>
      intro declaration member
      cases member
  | rule declaration k asked =>
      intro other member
      rw [List.mem_singleton] at member
      subst member
      exact ⟨inf_le_right, asked⟩
  | frame extra prior ih => exact ih
  | strengthen more prior ih =>
      intro declaration member
      exact ⟨inf_le_left.trans (ih declaration member).told,
        sys.guard_mono declaration inf_le_left (ih declaration member).asked⟩
  | @cut k k₁ k' Γ Γ₁ Γ' first second one two ihFirst ihSecond =>
      intro declaration member
      rcases List.mem_append.mp member with early | late
      · exact ⟨(Derives.refines two).trans (ihFirst declaration early).told,
          sys.guard_mono declaration (Derives.refines two) (ihFirst declaration early).asked⟩
      · exact ihSecond declaration late

/-- The linear zone of a proof is a multiplicative Horn derivation with the same leaves. -/
theorem Derives.horn {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') :
    ∃ diagram : LinearHorn.Derivation sys.premises sys.conclusions Γ Γ', diagram.uses = uses := by
  induction proof with
  | identity k Γ => exact ⟨.identity Γ, rfl⟩
  | rule declaration k asked => exact ⟨.rule declaration, rfl⟩
  | frame extra prior ih =>
      obtain ⟨diagram, same⟩ := ih
      refine ⟨.tensor diagram (.identity extra), ?_⟩
      simp only [LinearHorn.Derivation.uses, List.append_nil, same]
  | strengthen more prior ih => exact ih
  | cut first second ihFirst ihSecond =>
      obtain ⟨left, leftUses⟩ := ihFirst
      obtain ⟨right, rightUses⟩ := ihSecond
      refine ⟨.cut left right, ?_⟩
      simp only [LinearHorn.Derivation.uses, leftUses, rightUses]

/-- **The fibre reading.** A proof supplies a Horn derivation of its linear zone whose leaves are
all admitted at the final knowledge. -/
theorem Derives.fibre {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') :
    (∀ declaration ∈ uses, sys.AdmittedAt k' declaration) ∧
      ∃ diagram : LinearHorn.Derivation sys.premises sys.conclusions Γ Γ', diagram.uses = uses :=
  ⟨Derives.admitted proof, Derives.horn proof⟩

/-- A proof supplies a tensor sequent over its complete residual boundary. -/
theorem Derives.tensor_sequent {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Derives k Γ uses k' Γ') :
    ∃ sequent : TensorSequent.Derives sys.premises sys.conclusions (TensorSequent.atomContext Γ)
        (TensorSequent.Formula.ofMultiset Γ'), sequent.uses = uses := by
  obtain ⟨diagram, same⟩ := Derives.horn proof
  obtain ⟨sequent, sequentUses⟩ := TensorSequent.ofHornAtomic diagram
  exact ⟨sequent, sequentUses.trans same⟩

/-- No weakening: every additive invariant of the declarations is an invariant of proofs. -/
theorem Derives.preserves_valuation {Value : Type*} [AddMonoid Value] (value : Multiset Atom →+ Value)
    (balanced : ∀ declaration, value (sys.premises declaration) = value (sys.conclusions declaration))
    {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} (proof : sys.Derives k Γ uses k' Γ') :
    value Γ = value Γ' := by
  obtain ⟨diagram, _⟩ := Derives.horn proof
  exact diagram.preserves_valuation value balanced

/-- A Horn derivation whose leaves are admitted at a knowledge runs there and learns nothing. -/
theorem run_of_horn {k : K} {Γ Γ' : Multiset Atom}
    (diagram : LinearHorn.Derivation sys.premises sys.conclusions Γ Γ')
    (admitted : ∀ declaration ∈ diagram.uses, sys.AdmittedAt k declaration) :
    sys.Run k Γ diagram.uses k Γ' := by
  induction diagram with
  | identity context => exact Run.done k context
  | rule declaration =>
      have here := admitted declaration (List.mem_singleton.mpr rfl)
      have same : k ⊓ sys.tell declaration = k := inf_eq_left.mpr here.told
      have fires : sys.Fires declaration k (sys.premises declaration) k (sys.conclusions declaration) :=
        ⟨0, (add_zero _).symm, by rw [same]; exact here.asked, same.symm, (add_zero _).symm⟩
      exact Run.fire fires (Run.done _ _)
  | @tensor left right left' right' first second ihFirst ihSecond =>
      have one := ihFirst fun declaration member => admitted declaration (List.mem_append_left _ member)
      have two := ihSecond fun declaration member => admitted declaration (List.mem_append_right _ member)
      have later := Run.frame right two
      rw [add_comm left' right, add_comm right' right] at later
      exact Run.append (Run.frame left' one) later
  | cut first second ihFirst ihSecond =>
      exact Run.append
        (ihFirst fun declaration member => admitted declaration (List.mem_append_left _ member))
        (ihSecond fun declaration member => admitted declaration (List.mem_append_right _ member))

/-- **Runs that learn nothing are exactly Horn derivations over the admitted declarations.** -/
theorem run_iff_horn_of_stationary (k : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.Run k Γ uses k Γ' ↔
      (∀ declaration ∈ uses, sys.AdmittedAt k declaration) ∧
        ∃ diagram : LinearHorn.Derivation sys.premises sys.conclusions Γ Γ', diagram.uses = uses := by
  constructor
  · intro run
    exact Derives.fibre (Run.derives run)
  · rintro ⟨admitted, diagram, rfl⟩
    exact run_of_horn diagram admitted

/-! ## Forgetting knowledge in the conclusion -/

/-- A proof up to forgetting: the final knowledge of the proof refines the stated one. This is
the sequent whose conclusion may weaken persistent knowledge. -/
def DerivesUpTo (system : System K Atom Rule) (k : K) (Γ : Multiset Atom) (uses : List Rule)
    (weaker : K) (Γ' : Multiset Atom) : Prop :=
  ∃ k' : K, k' ≤ weaker ∧ system.Derives k Γ uses k' Γ'

/-- A proof up to forgetting exists exactly when a run reaches knowledge at least as strong. -/
theorem derivesUpTo_iff_run (k weaker : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    sys.DerivesUpTo k Γ uses weaker Γ' ↔ ∃ k' : K, k' ≤ weaker ∧ sys.Run k Γ uses k' Γ' :=
  ⟨fun ⟨k', below, proof⟩ => ⟨k', below, Derives.run proof⟩,
    fun ⟨k', below, run⟩ => ⟨k', below, Run.derives run⟩⟩

theorem DerivesUpTo.forget {k weaker weakest : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (above : weaker ≤ weakest) (proof : sys.DerivesUpTo k Γ uses weaker Γ') :
    sys.DerivesUpTo k Γ uses weakest Γ' := by
  obtain ⟨k', below, inner⟩ := proof
  exact ⟨k', below.trans above, inner⟩

/-- Cut up to forgetting: a proof from the forgotten knowledge still applies after a proof that
ends in stronger knowledge, because guards are stable under refinement. -/
theorem DerivesUpTo.cut {k middle weaker : K} {Γ Γ₁ Γ' : Multiset Atom} {first second : List Rule}
    (one : sys.DerivesUpTo k Γ first middle Γ₁) (two : sys.DerivesUpTo middle Γ₁ second weaker Γ') :
    sys.DerivesUpTo k Γ (first ++ second) weaker Γ' := by
  obtain ⟨k₁, below, early⟩ := one
  obtain ⟨k₂, below', late⟩ := two
  have later := Derives.strengthen k₁ late
  rw [inf_eq_right.mpr below] at later
  exact ⟨k₂ ⊓ k₁, inf_le_left.trans below', Derives.cut early later⟩

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
