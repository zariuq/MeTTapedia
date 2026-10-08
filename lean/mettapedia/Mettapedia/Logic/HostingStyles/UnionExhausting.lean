import Mettapedia.Logic.HostingStyles.Admissibility
import Mettapedia.Logic.HostingStyles.ReducingProofTheories
import Mettapedia.Logic.HostingStyles.ProofNodes

/-!
# When the inclusion of a member into a union is exhausting

There are two unions of proof systems, and the answer differs.

## The disjoint union: always

`sumSignature P` keeps the judgments of the members apart.  A derived rule of
the union whose assumptions and conclusion belong to one member uses the
rules of that member only, so it is the inclusion of a derived rule of the
member (`memberContext`, `inject_fill_memberContext`).  The inclusion is
exhausting, with the derivations kept apart and with no hypothesis
(`injectMap_exhausting`).  Hence the framework over the union hosts each
member with nothing added (`universalFramework_hostsExhaustively`).

## The union over shared judgments: exactly when the added rules are derivable

`P.withRule premises conclusion` adds one rule to a proof system on the same
judgments.

* At the level of provability, the inclusion is hosting, and it is exhausting
  **exactly when the added rule is derivable** in the system
  (`includeMap_exhausting_iff`).  An admissible rule that is not derivable
  changes no theorem and is not exhausted.
* With derivations kept apart, the inclusion is not exhausting as soon as
  every premise of the added rule has a derivation
  (`includeIdentityMap_not_exhausting`): the extended system then has a
  derivation that ends with the new rule, whatever the rule is.

## Examples

* Positive: the rule from `φ` to `φ`, derivable in every system
  (`identityRule_exhausting`).
* Negative: the rule from the atom `p` to the atom `q` in the worked logic.
  It is admissible, the two systems have the same theorems (existing
  `intPlus_proof_iff`), and the inclusion is not exhausting
  (`atomRule_not_exhausting`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

/-! ## The disjoint union -/

section Family

variable {Index : Type} {J : Index → Type} (P : (index : Index) → RuleSignature (J index))
  (index : Index) {arity : Type} (holes : arity → J index)

/-- The assumptions of a member, as assumptions of the union. -/
abbrev sumHoles : arity → Σ index, J index := fun slot => ⟨index, holes slot⟩

/-- The assumptions of a derived rule of the union, at a judgment of a
member: those whose judgment is that one. -/
abbrev MemberHole (member : Index) : PUnit.{1} → J member → Type :=
  fun _ j => {slot : arity // sumHoles index holes slot = (⟨member, j⟩ : Σ index, J index)}

/-- A derived rule of the union, read in the member that its conclusion
belongs to. -/
noncomputable def projectOpen {judgment : Σ index, J index}
    (observer : (sumSignature P).Open (sumHoles index holes) judgment) :
    (P judgment.1).Free (MemberHole index holes judgment.1) PUnit.unit judgment.2 :=
  Fix.fold ((sumSignature P).withHoles (RuleSignature.HoleAt (sumHoles index holes)))
    (carrier := fun _ judgment =>
      (P judgment.1).Free (MemberHole index holes judgment.1) PUnit.unit judgment.2)
    (fun _ judgment layer =>
      match layer with
      | ⟨.inl hole, _⟩ => Free.pure (P judgment.1) hole
      | ⟨.inr shape, children⟩ => Free.node (P judgment.1) shape children)
    PUnit.unit judgment observer

/-- **The derived rule of the member that a derived rule of the union is.** -/
noncomputable def memberContext {result : J index}
    (observer : (sumSignature P).Open (sumHoles index holes) ⟨index, result⟩) :
    (P index).Open holes result :=
  Free.map (P index)
    (fun _ j (hole : MemberHole index holes index PUnit.unit j) =>
      (⟨hole.1, eq_of_heq (Sigma.mk.inj hole.2).2⟩ : RuleSignature.HoleAt holes PUnit.unit j))
    PUnit.unit result (projectOpen P index holes observer)

/-- Filling a derived rule of the union with included derivations and reading
the result in the member is filling its reading. -/
theorem project_fill {judgment : Σ index, J index}
    (observer : (sumSignature P).Open (sumHoles index holes) judgment)
    (filling : (slot : arity) → (P index).Proof (holes slot)) :
    project P ((sumSignature P).fill observer fun slot => inject P index (filling slot)) =
      Free.fold (P judgment.1)
        (fun _ j (hole : MemberHole index holes judgment.1 PUnit.unit j) =>
          project P (RuleSignature.HoleAt.elim (motive := (sumSignature P).Proof)
            (fun slot => inject P index (filling slot)) (base := PUnit.unit)
            (hole : RuleSignature.HoleAt (sumHoles index holes) PUnit.unit ⟨judgment.1, j⟩)))
        (Algebra.initial (P judgment.1)) PUnit.unit judgment.2
        (projectOpen P index holes observer) := by
  induction observer using RuleSignature.Open.induction with
  | assume slot => rfl
  | @node judgment shape children ih =>
      change (P judgment.1).node shape (fun position =>
          project P ((sumSignature P).fill (children position)
            fun slot => inject P index (filling slot))) = _
      exact congrArg ((P judgment.1).node shape) (funext ih)

/-- **A derived rule of the union between judgments of a member acts on
included derivations as the inclusion of a derived rule of the member.** -/
theorem inject_fill_memberContext {result : J index}
    (observer : (sumSignature P).Open (sumHoles index holes) ⟨index, result⟩)
    (filling : (slot : arity) → (P index).Proof (holes slot)) :
    inject P index ((P index).fill (memberContext P index holes observer) filling) =
      (sumSignature P).fill observer fun slot => inject P index (filling slot) := by
  have member : (P index).fill (memberContext P index holes observer) filling =
      project P ((sumSignature P).fill observer fun slot => inject P index (filling slot)) := by
    rw [project_fill]
    unfold memberContext RuleSignature.fill Free.map
    rw [Free.fold_bind]
    congr 1
    funext base j hole
    obtain ⟨slot, same⟩ := hole
    cases base
    have equal : holes slot = j := eq_of_heq (Sigma.mk.inj same).2
    subst equal
    exact (project_inject P index (filling slot)).symm
  rw [member]
  exact inject_project P (judgment := ⟨index, result⟩)
    ((sumSignature P).fill observer fun slot => inject P index (filling slot))

/-- **The inclusion of a member into the disjoint union is exhausting**, with
the derivations kept apart. -/
theorem injectMap_exhausting : (injectMap P index).Exhausting := by
  intro arity holes result observer
  refine ⟨memberContext P index holes observer, fun filling => ?_⟩
  exact (inject_fill P index (memberContext P index holes observer) filling).symm.trans
    (inject_fill_memberContext P index holes observer filling)

/-- A member is hosted by the union with nothing added. -/
theorem sum_hostsExhaustively :
    HostsExhaustively
      ((sumSignature P).proofTheory (RuleSignature.ProofCongruence.identity _))
      ((P index).proofTheory (RuleSignature.ProofCongruence.identity _)) :=
  ⟨injectMap P index, injectMap_hosting P index, injectMap_exhausting P index⟩

/-- **The framework over the union hosts each member with nothing added.** -/
theorem universalFramework_hostsExhaustively (finitary : (index : Index) → (P index).Finitary) :
    HostsExhaustively (universalFramework P finitary)
      ((P index).proofTheory (RuleSignature.ProofCongruence.identity _)) :=
  (sum_hostsExhaustively P index).trans (universalFramework_exhausts_union P finitary)

end Family

/-! ## The union over shared judgments -/

namespace RuleSignature

variable {J : Type} (P : RuleSignature J) {count : Nat} (premises : Fin count → J) (conclusion : J)

/-- A derivation of the system, as a derivation of the system with one more
rule. -/
noncomputable def includeProof {j : J} (proof : P.Proof j) :
    (P.withRule premises conclusion).Proof j :=
  Fix.fold P (carrier := fun _ j => (P.withRule premises conclusion).Proof j)
    (fun _ _ layer => (P.withRule premises conclusion).node (.inl layer.1) layer.2)
    PUnit.unit j proof

/-- A derived rule of the system, as a derived rule of the extended system. -/
noncomputable def includeContext {arity : Type} {holes : arity → J} {j : J}
    (context : P.Open holes j) : (P.withRule premises conclusion).Open holes j :=
  Free.fold P (fun _ _ hole => Free.pure (P.withRule premises conclusion) hole)
    { act := fun _ _ layer => Free.node (P.withRule premises conclusion) (.inl layer.1) layer.2 }
    PUnit.unit j context

theorem includeProof_fill {arity : Type} {holes : arity → J} {j : J} (context : P.Open holes j)
    (filling : (index : arity) → P.Proof (holes index)) :
    P.includeProof premises conclusion (P.fill context filling) =
      (P.withRule premises conclusion).fill (P.includeContext premises conclusion context)
        fun index => P.includeProof premises conclusion (filling index) := by
  induction context using RuleSignature.Open.induction with
  | assume index => rfl
  | node shape children ih =>
      change (P.withRule premises conclusion).node (.inl shape)
          (fun position => P.includeProof premises conclusion (P.fill (children position) filling)) =
        (P.withRule premises conclusion).node (.inl shape) _
      exact congrArg _ (funext ih)

/-- **The inclusion into the system with one more rule**, at the level of
provability. -/
noncomputable def includeMap :
    ContextMap (P.proofTheory (ProofCongruence.total P))
      ((P.withRule premises conclusion).proofTheory (ProofCongruence.total _)) where
  interface := fun j => j
  term := fun proof => P.includeProof premises conclusion proof
  context := fun context => P.includeContext premises conclusion context
  term_resp := fun _ => trivial
  equivariant := fun _ _ => trivial

/-- At the level of provability the inclusion is hosting, for every rule. -/
theorem includeMap_hosting : (P.includeMap premises conclusion).Hosting := by
  rw [P.hosting_iff_static _ (P.includeMap premises conclusion) fun _ _ step => step]
  exact fun _ => trivial

/-- Replace every use of the added rule by a derivation of it. -/
noncomputable def eliminateRule (derived : P.Open premises conclusion) {arity : Type}
    {holes : arity → J} {j : J} (context : (P.withRule premises conclusion).Open holes j) :
    P.Open holes j :=
  Free.fold (P.withRule premises conclusion) (fun _ _ hole => Free.pure P hole)
    { act := fun _ _ layer =>
        match layer with
        | ⟨.inl old, children⟩ => Free.node P old children
        | ⟨.inr ⟨same⟩, children⟩ =>
            same ▸ Free.bind P
              (fun _ _ hole => HoleAt.elim (motive := P.Open holes) children hole)
              PUnit.unit conclusion derived }
    PUnit.unit j context

/-- **At the level of provability, the inclusion is exhausting exactly when
the added rule is derivable.** -/
theorem includeMap_exhausting_iff :
    (P.includeMap premises conclusion).Exhausting ↔ P.DerivableRule premises conclusion := by
  constructor
  · intro exhausting
    obtain ⟨context, -⟩ := exhausting (holes := premises) (result := conclusion)
      (Free.node (P.withRule premises conclusion) (.inr ⟨rfl⟩) fun index =>
        (P.withRule premises conclusion).assume index)
    exact ⟨context⟩
  · rintro ⟨derived⟩ arity holes result observer
    exact ⟨P.eliminateRule premises conclusion derived observer, fun _ => trivial⟩

/-- The inclusion, with derivations kept apart. -/
noncomputable def includeIdentityMap :
    ContextMap (P.proofTheory (ProofCongruence.identity P))
      ((P.withRule premises conclusion).proofTheory (ProofCongruence.identity _)) where
  interface := fun j => j
  term := fun proof => P.includeProof premises conclusion proof
  context := fun context => P.includeContext premises conclusion context
  term_resp := fun same => congrArg (P.includeProof premises conclusion) same
  equivariant := fun context filling => P.includeProof_fill premises conclusion context filling

/-- **With derivations kept apart, the inclusion is not exhausting as soon as
every premise of the added rule has a derivation**: the derivation that ends
with the new rule is the inclusion of none. -/
theorem includeIdentityMap_not_exhausting
    (each : ∀ index, Nonempty (P.Proof (premises index))) :
    ¬ (P.includeIdentityMap premises conclusion).Exhausting := by
  intro exhausting
  obtain ⟨preimage, same⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := conclusion)
    ((P.withRule premises conclusion).node (.inr ⟨rfl⟩) fun index =>
      P.includeProof premises conclusion (Classical.choice (each index)))
  obtain ⟨shape, children, rfl⟩ := Proof.exists_node P preimage
  have written : (P.withRule premises conclusion).node (.inr ⟨rfl⟩)
      (fun index => P.includeProof premises conclusion (Classical.choice (each index))) =
      (P.withRule premises conclusion).node (.inl shape)
        (fun position => P.includeProof premises conclusion (children position)) := same
  have roots := congrArg (P.withRule premises conclusion).rootShape written
  cases roots

end RuleSignature

/-! ## Examples -/

/-- **Positive**: the rule from a judgment to itself is derivable in every
system, so adding it is exhausted at the level of provability. -/
theorem identityRule_exhausting {J : Type} (P : RuleSignature J) (j : J) :
    (P.includeMap (fun _ : Fin 1 => j) j).Exhausting :=
  (P.includeMap_exhausting_iff (fun _ : Fin 1 => j) j).mpr ⟨P.assume (holes := fun _ : Fin 1 => j) 0⟩

/-- **Negative**: the rule from the atom `p` to the atom `q` is admissible in
the worked logic and not derivable, so adding it is hosting and not
exhausting. -/
theorem atomRule_not_exhausting :
    (intSignature.includeMap atomPremise atomConclusion).Hosting ∧
      ¬ (intSignature.includeMap atomPremise atomConclusion).Exhausting :=
  ⟨intSignature.includeMap_hosting atomPremise atomConclusion, fun exhausting =>
    atomRule_not_derivable
      ((intSignature.includeMap_exhausting_iff atomPremise atomConclusion).mp exhausting)⟩

/-- The rule from `φ ➝ φ` to itself: derivable, exhausted at the level of
provability, and not exhausted with derivations kept apart. -/
theorem identityRule_two_levels (φ : IntFormula) :
    (intSignature.includeMap (fun _ : Fin 1 => (φ ➝ φ : IntFormula)) (φ ➝ φ)).Exhausting ∧
      ¬ (intSignature.includeIdentityMap (fun _ : Fin 1 => (φ ➝ φ : IntFormula))
        (φ ➝ φ)).Exhausting :=
  ⟨identityRule_exhausting intSignature (φ ➝ φ),
    intSignature.includeIdentityMap_not_exhausting _ _ fun _ => ⟨identityProof φ⟩⟩

#print axioms inject_fill_memberContext
#print axioms injectMap_exhausting
#print axioms universalFramework_hostsExhaustively
#print axioms RuleSignature.includeMap_exhausting_iff
#print axioms RuleSignature.includeIdentityMap_not_exhausting
#print axioms identityRule_exhausting
#print axioms atomRule_not_exhausting
#print axioms identityRule_two_levels

end Mettapedia.Logic.HostingStyles
