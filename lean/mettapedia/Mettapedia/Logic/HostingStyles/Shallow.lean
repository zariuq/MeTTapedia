import Mettapedia.Logic.HostingStyles.ProofTheory

/-!
# Native and shallow semantic hosting, as maps of theories

Two of the three ways of hosting a proof system, stated in the category of
theories presented through their contexts.

## Native

The host holds the derivations themselves.  As a map of theories this is the
identity, which is hosting and exhausting (`native_hosting`,
`native_exhausting`).  The system's own checker enters through the existing
replay of certificate trees: a judgment has an accepted certificate exactly
when it has a derivation (`accepted_iff_nonempty_proof`).

## Shallow semantic

A shallow semantic embedding gives every judgment a host proposition at each
point of evaluation (a world of a model): `holds point j`.  The host has no
object derivations.  What it has is

* the truth of a judgment at every point (`Valid`), and
* entailments between judgments, from finitely many of the assumptions
  (`Entails`).

These are the terms and contexts of a theory, `shallowTheory`.  Any two terms
of one interface are equal there: a host proposition has at most one proof.

When every rule preserves truth at each point (`LocallySound`), the proof
system maps into that theory (`shallowMap`): a derivation goes to the truth of
its conclusion, a derived rule to an entailment.  This map is the soundness
theorem, and the two non-degeneracy conditions read as follows.

* **Hosting** holds exactly when the source already identifies all
  derivations of a judgment (`shallowMap_hosting_iff`).  So the embedding is
  hosting for the provability collapse of the proof system
  (`shallowMap_hosting_total`), and is not hosting as soon as derivations are
  kept apart and some judgment has two (`shallowMap_not_hosting`).
* **Exhausting** holds exactly when every entailment of the host comes from a
  derived rule (`shallowMap_exhausting_iff`).  On judgments alone this is
  completeness (`complete_of_exhausting`); together with soundness it is the
  faithfulness of the embedding: derivable exactly when valid
  (`derivable_iff_valid`).  A host that validates more than the proof system
  derives is not exhausted (`not_exhausting_of_valid_underivable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT

universe v

/-! ## Native hosting -/

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-- **Native presentation is the identity map**, and it is hosting: nothing
of the proof system is lost. -/
theorem native_hosting (congruence : P.ProofCongruence) :
    (ContextMap.id (P.proofTheory congruence)).Hosting :=
  ContextMap.hosting_id _

/-- Native presentation is exhausting: the host adds nothing. -/
theorem native_exhausting (congruence : P.ProofCongruence) :
    (ContextMap.id (P.proofTheory congruence)).Exhausting :=
  ContextMap.exhausting_id _

/-- **The system's own checker accepts exactly the derivable judgments.**
For any decidable presentation of the rule instances, a judgment has a
certificate tree accepted by the existing replay exactly when it has a
derivation. -/
theorem accepted_iff_nonempty_proof (finitary : P.Finitary)
    (witnesses : Mettapedia.Logic.RuleWitness finitary.rules) (j : J) :
    (∃ certificate : Mettapedia.Logic.Derivation J witnesses.W,
        certificate.valid witnesses = true ∧ certificate.concl = j) ↔
      Nonempty (P.Proof j) := by
  rw [nonempty_proof_iff_derives finitary]
  constructor
  · rintro ⟨certificate, accepted, rfl⟩
    exact certificate.valid_sound witnesses accepted
  · exact fun derives => Mettapedia.Logic.Derives.exists_derivation witnesses derives

end RuleSignature

/-! ## The theory of a semantics -/

section Semantics

variable {J : Type} {Point : Type v} (holds : Point → J → Prop)

/-- A judgment is valid when it holds at every point. -/
def Valid (j : J) : Prop := ∀ point, holds point j

/-- The conclusion holds at every point where finitely many of the
assumptions hold. -/
def Entails {arity : Type} (assumptions : arity → J) (conclusion : J) : Prop :=
  ∃ support : List arity, ∀ point,
    (∀ index ∈ support, holds point (assumptions index)) → holds point conclusion

variable {holds}

theorem Entails.assume {arity : Type} (assumptions : arity → J) (index : arity) :
    Entails holds assumptions (assumptions index) :=
  ⟨[index], fun _ assumed => assumed index List.mem_cons_self⟩

theorem Entails.of_valid {arity : Type} (assumptions : arity → J) {conclusion : J}
    (valid : Valid holds conclusion) : Entails holds assumptions conclusion :=
  ⟨[], fun point _ => valid point⟩

theorem Entails.valid {arity : Type} {assumptions : arity → J} {conclusion : J}
    (entails : Entails holds assumptions conclusion)
    (valid : ∀ index, Valid holds (assumptions index)) : Valid holds conclusion := by
  obtain ⟨support, follows⟩ := entails
  exact fun point => follows point fun index _ => valid index point

/-- Rename the assumptions. -/
theorem Entails.map {arity newArity : Type} {assumptions : arity → J}
    {newAssumptions : newArity → J} (rename : arity → newArity)
    (same : ∀ index, newAssumptions (rename index) = assumptions index) {conclusion : J}
    (entails : Entails holds assumptions conclusion) :
    Entails holds newAssumptions conclusion := by
  obtain ⟨support, follows⟩ := entails
  refine ⟨support.map rename, fun point assumed => follows point fun index member => ?_⟩
  rw [← same index]
  exact assumed (rename index) (List.mem_map_of_mem member)

/-- Finitely many entailments from the same assumptions share one finite
support. -/
theorem Entails.all {arity goalIndex : Type} {assumptions : arity → J} {goals : goalIndex → J}
    (each : ∀ goal, Entails holds assumptions (goals goal)) (selected : List goalIndex) :
    ∃ support : List arity, ∀ point,
      (∀ index ∈ support, holds point (assumptions index)) →
        ∀ goal ∈ selected, holds point (goals goal) := by
  induction selected with
  | nil => exact ⟨[], fun _ _ _ member => absurd member List.not_mem_nil⟩
  | cons head tail ih =>
      obtain ⟨rest, restFollows⟩ := ih
      obtain ⟨support, follows⟩ := each head
      refine ⟨support ++ rest, fun point assumed goal member => ?_⟩
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact follows point fun index indexMember =>
          assumed index (List.mem_append_left _ indexMember)
      · exact restFollows point
          (fun index indexMember => assumed index (List.mem_append_right _ indexMember))
          goal member

/-- Entailment composes. -/
theorem Entails.trans {arity goalIndex : Type} {assumptions : arity → J}
    {goals : goalIndex → J} {conclusion : J} (outer : Entails holds goals conclusion)
    (each : ∀ goal, Entails holds assumptions (goals goal)) :
    Entails holds assumptions conclusion := by
  obtain ⟨selected, follows⟩ := outer
  obtain ⟨support, all⟩ := Entails.all each selected
  exact ⟨support, fun point assumed => follows point (all point assumed)⟩

variable (holds)

/-- Any two proofs of one host proposition are equal. -/
theorem plift_eq {proposition : Prop} (first second : PLift proposition) : first = second := by
  cases first
  cases second
  rfl

/-- **The theory of a semantics.**  An interface is a judgment, a term of it
is the truth of the judgment at every point, a context is an entailment.  Any
two terms of an interface are equal, and nothing reduces. -/
def shallowTheory : ContextTheory.{0} where
  Interface := J
  Term := fun j => PLift (Valid holds j)
  equations := fun _ => ⟨fun _ _ => True, fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ step => step.elim
  rewrites_resp_right := fun step _ => step
  Context := fun holes result => PLift (Entails holds holes result)
  fill := fun context filling => ⟨context.down.valid fun index => (filling index).down⟩
  fill_resp := fun _ _ _ _ => trivial
  identity := fun j => ⟨Entails.assume (fun _ : Unit => j) ()⟩
  fill_identity := fun _ _ => plift_eq _ _
  plug := fun context inner =>
    ⟨context.down.trans fun index =>
      (inner index).down.map (Sigma.mk index) fun _ => rfl⟩
  fill_plug := fun _ _ _ => plift_eq _ _
  relabel := fun rename _ context => ⟨context.down.map rename fun _ => rfl⟩
  fill_relabel := fun _ _ _ _ => plift_eq _ _
  constant := fun term => ⟨Entails.of_valid _ term.down⟩
  fill_constant := fun _ _ => plift_eq _ _

/-! ## The shallow map: soundness -/

variable (P : RuleSignature J)

/-- Every rule preserves truth at each point. -/
def LocallySound : Prop :=
  ∀ {j : J} (shape : P.Shape PUnit.unit j) (point : Point),
    (∀ position, holds point (P.next shape position)) → holds point j

variable {holds P}

/-- **Soundness, as a fold**: the conclusion of a derivation is valid. -/
theorem LocallySound.valid (sound : LocallySound holds P) {j : J} (proof : P.Proof j) :
    Valid holds j := by
  induction proof using RuleSignature.Proof.induction with
  | node shape children ih => exact fun point => sound shape point fun position => ih position point

/-- Soundness for derived rules: a derivation from assumptions gives an
entailment from finitely many of them. -/
theorem LocallySound.entails (sound : LocallySound holds P) (finitary : P.Finitary)
    {arity : Type} {assumptions : arity → J} {j : J} (context : P.Open assumptions j) :
    Entails holds assumptions j := by
  induction context using RuleSignature.Open.induction with
  | assume index => exact Entails.assume assumptions index
  | node shape children ih =>
      obtain ⟨support, all⟩ := Entails.all ih (finitary.positions shape)
      exact ⟨support, fun point assumed => sound shape point fun position =>
        all point assumed position (finitary.complete shape position)⟩

/-- **The shallow semantic embedding, as a map of theories.**  A derivation
goes to the truth of its conclusion and a derived rule to an entailment. -/
noncomputable def shallowMap (sound : LocallySound holds P) (finitary : P.Finitary)
    (congruence : P.ProofCongruence) :
    ContextMap (P.proofTheory congruence) (shallowTheory holds) where
  interface := fun j => j
  term := fun proof => ⟨sound.valid proof⟩
  context := fun context => ⟨sound.entails finitary context⟩
  term_resp := fun _ => trivial
  equivariant := fun _ _ => trivial

/-! ## Hosting -/

/-- **A shallow embedding is hosting exactly when the source already
identifies all derivations of each judgment.** -/
theorem shallowMap_hosting_iff (sound : LocallySound holds P) (finitary : P.Finitary)
    (congruence : P.ProofCongruence) :
    (shallowMap sound finitary congruence).Hosting ↔
      (RuleSignature.ProofCongruence.total P).Refines congruence := by
  rw [P.hosting_iff_static congruence _ (fun _ _ step => step)]
  exact ⟨fun reflects _ _ _ _ => reflects trivial, fun all _ _ _ _ => all trivial⟩

/-- A shallow embedding is hosting for the provability collapse. -/
theorem shallowMap_hosting_total (sound : LocallySound holds P) (finitary : P.Finitary) :
    (shallowMap sound finitary (RuleSignature.ProofCongruence.total P)).Hosting :=
  (shallowMap_hosting_iff sound finitary _).mpr fun related => related

/-- **A shallow embedding is not hosting for a congruence that keeps two
derivations of one judgment apart.** -/
theorem shallowMap_not_hosting (sound : LocallySound holds P) (finitary : P.Finitary)
    (congruence : P.ProofCongruence) {j : J} {first second : P.Proof j}
    (apart : ¬ (congruence.setoid j).r first second) :
    ¬ (shallowMap sound finitary congruence).Hosting :=
  ContextMap.not_hosting_of_identifies _ apart trivial

/-! ## Exhausting: completeness -/

variable (holds P)

/-- Every valid judgment has a derivation. -/
def Complete : Prop := ∀ j : J, Valid holds j → Nonempty (P.Proof j)

/-- Every entailment of the host comes from a derived rule. -/
def StronglyComplete : Prop :=
  ∀ (arity : Type) (assumptions : arity → J) (conclusion : J),
    Entails holds assumptions conclusion → Nonempty (P.Open assumptions conclusion)

variable {holds P}

theorem StronglyComplete.complete (strong : StronglyComplete holds P) : Complete holds P := by
  intro j valid
  obtain ⟨context⟩ := strong Empty (fun index => index.elim) j (Entails.of_valid _ valid)
  exact ⟨P.fill context fun index => index.elim⟩

/-- **A shallow embedding is exhausting exactly when every host entailment
comes from a derived rule.** -/
theorem shallowMap_exhausting_iff (sound : LocallySound holds P) (finitary : P.Finitary)
    (congruence : P.ProofCongruence) :
    (shallowMap sound finitary congruence).Exhausting ↔ StronglyComplete holds P := by
  constructor
  · intro exhausting arity assumptions conclusion entails
    obtain ⟨context, _⟩ := exhausting (holes := assumptions) (result := conclusion) ⟨entails⟩
    exact ⟨context⟩
  · intro strong arity assumptions conclusion observer
    obtain ⟨context⟩ := strong arity assumptions conclusion observer.down
    exact ⟨context, fun _ => trivial⟩

/-- An exhausting shallow embedding is complete. -/
theorem complete_of_exhausting (sound : LocallySound holds P) (finitary : P.Finitary)
    (congruence : P.ProofCongruence)
    (exhausting : (shallowMap sound finitary congruence).Exhausting) : Complete holds P :=
  ((shallowMap_exhausting_iff sound finitary congruence).mp exhausting).complete

/-- **Faithfulness of a shallow embedding**: derivable exactly when valid.
Soundness is the map; completeness is what exhausting gives on judgments. -/
theorem derivable_iff_valid (sound : LocallySound holds P) (complete : Complete holds P)
    (j : J) : Nonempty (P.Proof j) ↔ Valid holds j :=
  ⟨fun ⟨proof⟩ => sound.valid proof, complete j⟩

/-- **A host that validates an underivable judgment is not exhausted**: it
holds a term that no derivation reaches. -/
theorem not_exhausting_of_valid_underivable (sound : LocallySound holds P)
    (finitary : P.Finitary) (congruence : P.ProofCongruence) {j : J}
    (valid : Valid holds j) (underivable : IsEmpty (P.Proof j)) :
    ¬ (shallowMap sound finitary congruence).Exhausting := fun exhausting =>
  (complete_of_exhausting sound finitary congruence exhausting j valid).elim underivable.false

/-- **Independence by a countermodel.**  Under soundness alone, a judgment
that fails at one point has no derivation. -/
theorem isEmpty_proof_of_countermodel (sound : LocallySound holds P) {j : J} {point : Point}
    (fails : ¬ holds point j) : IsEmpty (P.Proof j) :=
  ⟨fun proof => fails (sound.valid proof point)⟩

end Semantics

#print axioms RuleSignature.accepted_iff_nonempty_proof
#print axioms shallowTheory
#print axioms shallowMap
#print axioms shallowMap_hosting_iff
#print axioms shallowMap_not_hosting
#print axioms shallowMap_exhausting_iff
#print axioms derivable_iff_valid
#print axioms not_exhausting_of_valid_underivable

end Mettapedia.Logic.HostingStyles
