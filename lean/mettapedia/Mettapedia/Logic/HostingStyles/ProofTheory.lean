import Mettapedia.TypeTheory.IndexedPolynomialFree
import Mettapedia.GSLT.Contexts.ContextMorphism
import Mettapedia.Logic.Derivation

/-!
# Proof systems as theories presented through their contexts

A proof system has judgments, rules and derivations.  Nothing new is needed
to state that:

* a **rule signature** over judgments `J` is an indexed polynomial over `J`
  (`Mettapedia.TypeTheory.IndexedPolynomial`): a shape is a rule instance
  with its conclusion, a position is one of its premises;
* a **derivation** is an element of the polynomial's fixed family `Fix`;
* a **derived rule**, a derivation from assumptions, is an element of the
  free family `Free`: a tree whose leaves may be holes, each at a judgment.

This module adds the one missing bridge: the derivations and derived rules of
a rule signature are the terms and contexts of a `ContextTheory`
(`Mettapedia.GSLT.Contexts`), so that hostings of a proof system are maps of
theories and the existing `Hosting` and `Exhausting` conditions apply.

* An interface is a judgment, a term of it is a derivation of it, a context
  is a derived rule, and filling plugs derivations into the holes.
* The static equivalence is a parameter: a `ProofCongruence` says when two
  derivations of one judgment count as the same.  Equality keeps every
  derivation apart.  The total congruence keeps only whether a judgment has a
  derivation.
* A proof system has no reduction.  Every probe therefore finds any two
  derivations of one judgment bisimilar (`bisimilar_all`); what a host keeps
  or forgets about a proof system is read from the static equivalence, and
  the hosting condition reduces to reflecting it (`hosting_iff_static`).
* Coarsening the congruence is a map of theories.  It is hosting exactly when
  it identifies nothing new (`coarsen_hosting_iff`).

For a signature whose rules have finitely many premises, having a derivation
is derivability in the existing finitary rule closure `Mettapedia.Logic.Derives`
(`nonempty_proof_iff_derives`), and the number of rule nodes of a derivation
is a fold (`size`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT

/-- A rule signature over the judgments `J`: an indexed polynomial whose
shapes at a judgment are the rule instances concluding it and whose positions
are the premises. -/
abbrev RuleSignature (J : Type) : Type 1 :=
  IndexedPolynomial.{0, 0, 0, 0} PUnit.{1} (fun _ : PUnit.{1} => J)

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-- The derivations of a judgment. -/
abbrev Proof (j : J) : Type := P.Fix PUnit.unit j

/-- One rule application: a rule instance and a derivation of each premise. -/
abbrev node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    P.Proof j :=
  .roll shape children

/-- The holes of an indexed family of assumptions, sorted by judgment. -/
abbrev HoleAt {arity : Type} (holes : arity → J) : PUnit.{1} → J → Type :=
  fun _ j => {index : arity // holes index = j}

/-- Use a hole of the family as the assumption it stands for. -/
def HoleAt.elim {arity : Type} {holes : arity → J} {motive : J → Sort*}
    (value : (index : arity) → motive (holes index))
    {base : PUnit.{1}} {j : J} (hole : HoleAt holes base j) : motive j :=
  hole.2 ▸ value hole.1

/-- The hole standing for one assumption. -/
def HoleAt.mk {arity : Type} {holes : arity → J} (index : arity) :
    HoleAt holes PUnit.unit (holes index) := ⟨index, rfl⟩

@[simp] theorem HoleAt.elim_mk {arity : Type} {holes : arity → J} {motive : J → Sort*}
    (value : (index : arity) → motive (holes index)) (index : arity) :
    HoleAt.elim (motive := motive) value (HoleAt.mk (holes := holes) index) = value index := rfl

/-- The derived rules with the given assumptions and conclusion: derivations
with holes. -/
abbrev Open {arity : Type} (holes : arity → J) (j : J) : Type :=
  P.Free (HoleAt holes) PUnit.unit j

/-- The derived rule that is one assumption. -/
abbrev assume {arity : Type} {holes : arity → J} (index : arity) : P.Open holes (holes index) :=
  Free.pure P (HoleAt.mk index)

/-- Induction on derivations. -/
@[elab_as_elim]
theorem Proof.induction {motive : (j : J) → P.Proof j → Prop}
    (node : ∀ {j : J} (shape : P.Shape PUnit.unit j)
      (children : (position : P.Position shape) → P.Proof (P.next shape position)),
      (∀ position, motive _ (children position)) → motive j (P.node shape children))
    {j : J} (proof : P.Proof j) : motive j proof :=
  @Fix.rec PUnit.{1} (fun _ => J) P PUnit.unit (fun j proof => motive j proof)
    (fun shape children hypotheses => node shape children hypotheses) j proof

/-- Induction on derived rules: an assumption, or a rule applied to derived
rules. -/
@[elab_as_elim]
theorem Open.induction {arity : Type} {holes : arity → J}
    {motive : (j : J) → P.Open holes j → Prop}
    (assume : ∀ index : arity, motive _ (P.assume index))
    (node : ∀ {j : J} (shape : P.Shape PUnit.unit j)
      (children : (position : P.Position shape) → P.Open holes (P.next shape position)),
      (∀ position, motive _ (children position)) → motive j (Free.node P shape children))
    {j : J} (context : P.Open holes j) : motive j context :=
  @Fix.rec PUnit.{1} (fun _ => J) (P.withHoles (HoleAt holes)) PUnit.unit
    (fun j context => motive j context)
    (fun {j} shape children hypotheses => by
      cases shape with
      | inl hole =>
          rcases hole with ⟨index, rfl⟩
          have same : children = fun position => position.elim := by
            funext position
            exact position.elim
          subst same
          exact assume index
      | inr shape => exact node shape children hypotheses) j context

/-! ## Filling, plugging, renaming -/

/-- Fill every hole with a derivation of its judgment. -/
noncomputable def fill {arity : Type} {holes : arity → J} {result : J}
    (context : P.Open holes result) (filling : (index : arity) → P.Proof (holes index)) :
    P.Proof result :=
  Free.fold P (fun _ _ hole => HoleAt.elim (motive := P.Proof) filling hole)
    (Algebra.initial P) PUnit.unit result context

@[simp] theorem fill_assume {arity : Type} {holes : arity → J}
    (filling : (index : arity) → P.Proof (holes index)) (index : arity) :
    P.fill (P.assume index) filling = filling index := rfl

@[simp] theorem fill_node {arity : Type} {holes : arity → J} {j : J}
    (filling : (index : arity) → P.Proof (holes index)) (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Open holes (P.next shape position)) :
    P.fill (Free.node P shape children) filling =
      P.node shape fun position => P.fill (children position) filling := rfl

/-- Plug a family of derived rules into the holes of a derived rule. -/
noncomputable def plug {arity : Type} {holes : arity → J} {result : J}
    {innerArity : arity → Type} {innerHoles : (index : arity) → innerArity index → J}
    (context : P.Open holes result)
    (inner : (index : arity) → P.Open (innerHoles index) (holes index)) :
    P.Open (fun position : Σ index, innerArity index => innerHoles position.1 position.2)
      result :=
  Free.bind P
    (fun _ _ hole => HoleAt.elim
      (motive := P.Open
        (fun position : Σ index, innerArity index => innerHoles position.1 position.2))
      (fun index => Free.map P
        (fun _ _ leaf => (⟨⟨index, leaf.1⟩, leaf.2⟩ :
          HoleAt (fun position : Σ index, innerArity index =>
            innerHoles position.1 position.2) _ _))
        PUnit.unit (holes index) (inner index)) hole)
    PUnit.unit result context

/-- Rename the holes. -/
noncomputable def relabel {arity newArity : Type} {holes : newArity → J} {result : J}
    (rename : arity → newArity) (context : P.Open (fun index => holes (rename index)) result) :
    P.Open holes result :=
  Free.map P (fun _ _ hole => (⟨rename hole.1, hole.2⟩ : HoleAt holes _ _)) PUnit.unit result
    context

/-- A derivation, as a derived rule that uses no assumption. -/
noncomputable def close {arity : Type} {holes : arity → J} {j : J} (proof : P.Proof j) :
    P.Open holes j :=
  Fix.fold P (Free.algebra P).act PUnit.unit j proof

@[simp] theorem close_node {arity : Type} {holes : arity → J} {j : J}
    (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    P.close (holes := holes) (P.node shape children) =
      Free.node P shape fun position => P.close (children position) := rfl

theorem fill_plug {arity : Type} {holes : arity → J} {result : J}
    {innerArity : arity → Type} {innerHoles : (index : arity) → innerArity index → J}
    (context : P.Open holes result)
    (inner : (index : arity) → P.Open (innerHoles index) (holes index))
    (filling : (position : Σ index, innerArity index) →
      P.Proof (innerHoles position.1 position.2)) :
    P.fill (P.plug context inner) filling =
      P.fill context fun index => P.fill (inner index) fun position =>
        filling ⟨index, position⟩ := by
  unfold fill plug
  rw [Free.fold_bind]
  congr 1
  funext base j hole
  rcases hole with ⟨index, rfl⟩
  cases base
  simp only [HoleAt.elim]
  unfold Free.map
  rw [Free.fold_bind]
  rfl

theorem fill_relabel {arity newArity : Type} {holes : newArity → J} {result : J}
    (rename : arity → newArity) (context : P.Open (fun index => holes (rename index)) result)
    (filling : (index : newArity) → P.Proof (holes index)) :
    P.fill (P.relabel rename context) filling =
      P.fill context fun index => filling (rename index) := by
  unfold fill relabel Free.map
  rw [Free.fold_bind]
  rfl

theorem fill_close {arity : Type} {holes : arity → J} {j : J} (proof : P.Proof j)
    (filling : (index : arity) → P.Proof (holes index)) :
    P.fill (P.close proof) filling = proof := by
  induction proof using Proof.induction with
  | node shape children ih =>
      change P.node shape (fun position => P.fill (P.close (children position)) filling) = _
      congr 1
      funext position
      exact ih position

/-! ## When two derivations count as the same -/

/-- A congruence on derivations: an equivalence on the derivations of each
judgment that every rule respects. -/
structure ProofCongruence where
  setoid : (j : J) → Setoid (P.Proof j)
  node : ∀ {j : J} (shape : P.Shape PUnit.unit j)
    (first second : (position : P.Position shape) → P.Proof (P.next shape position)),
    (∀ position, (setoid _).r (first position) (second position)) →
      (setoid j).r (P.node shape first) (P.node shape second)

namespace ProofCongruence

/-- Every derivation is kept apart. -/
def identity : P.ProofCongruence where
  setoid := fun _ => ⟨Eq, eq_equivalence⟩
  node := fun shape first second related => by
    have same : first = second := funext related
    subst same
    exact rfl

/-- Only the existence of a derivation is kept. -/
def total : P.ProofCongruence where
  setoid := fun _ => ⟨fun _ _ => True, fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  node := fun _ _ _ _ => trivial

variable {P}

/-- One congruence keeps at least the distinctions of another. -/
def Refines (fine coarse : P.ProofCongruence) : Prop :=
  ∀ {j : J} {first second : P.Proof j},
    (fine.setoid j).r first second → (coarse.setoid j).r first second

theorem identity_refines (congruence : P.ProofCongruence) :
    (identity P).Refines congruence := by
  intro j first second same
  cases same
  exact (congruence.setoid j).iseqv.refl first

theorem refines_total (congruence : P.ProofCongruence) : congruence.Refines (total P) :=
  fun _ => trivial

end ProofCongruence

theorem fill_resp (congruence : P.ProofCongruence) {arity : Type} {holes : arity → J}
    {result : J} (context : P.Open holes result)
    {first second : (index : arity) → P.Proof (holes index)}
    (related : ∀ index, (congruence.setoid _).r (first index) (second index)) :
    (congruence.setoid result).r (P.fill context first) (P.fill context second) := by
  induction context using Open.induction with
  | assume index => exact related index
  | node shape children ih => exact congruence.node shape _ _ fun position => ih position

/-! ## The theory of a rule signature -/

/-- **The theory presented by a rule signature**, at a chosen congruence on
derivations.  An interface is a judgment, a term is a derivation, a context is
a derived rule; there is no reduction. -/
noncomputable def proofTheory (congruence : P.ProofCongruence) : ContextTheory.{0} where
  Interface := J
  Term := P.Proof
  equations := congruence.setoid
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ step => step.elim
  rewrites_resp_right := fun step _ => step
  Context := fun holes result => P.Open holes result
  fill := P.fill
  fill_resp := fun context _ _ related => P.fill_resp congruence context related
  identity := fun j => P.assume (holes := fun _ : Unit => j) ()
  fill_identity := fun _ _ => rfl
  plug := P.plug
  fill_plug := P.fill_plug
  relabel := fun rename _ context => P.relabel rename context
  fill_relabel := fun rename _ context filling => P.fill_relabel rename context filling
  constant := fun term => P.close term
  fill_constant := fun term filling => P.fill_close term filling

/-- A proof system has no transition. -/
theorem not_transition (congruence : P.ProofCongruence) {source target : J}
    (term : (P.proofTheory congruence).Term source)
    (label : (P.proofTheory congruence).Label source target)
    (next : (P.proofTheory congruence).Term target) :
    ¬ (P.proofTheory congruence).Transition term label next :=
  fun step => step

/-- **Every probe finds any two derivations of one judgment bisimilar**: a
proof system has no transition for an observer to label. -/
theorem bisimilar_all (congruence : P.ProofCongruence)
    (probe : (P.proofTheory congruence).Probe) {index : probe.Index}
    (left right : (P.proofTheory congruence).Term (probe.interface index)) :
    probe.Bisimilar left right :=
  ⟨fun _ _ _ => True, ⟨fun _ _ _ _ step => step.elim, fun _ _ _ _ step => step.elim⟩, trivial⟩

/-- For a map out of the theory of a rule signature into a theory without
reduction, hosting is reflecting the congruence. -/
theorem hosting_iff_static (congruence : P.ProofCongruence) {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory congruence) target)
    (static : ∀ {interface : target.Interface} (term next : target.Term interface),
      ¬ target.rewrites term next) :
    map.Hosting ↔ map.ReflectsEquations := by
  rw [ContextMap.hosting_iff]
  exact ⟨fun laws => laws.1, fun reflects =>
    ⟨reflects, fun _ _ _ step => step.elim, fun _ _ _ step => (static _ _ step).elim⟩⟩

/-! ## Coarsening the congruence -/

/-- Forgetting distinctions between derivations is a map of theories. -/
noncomputable def coarsen {fine coarse : P.ProofCongruence} (refines : fine.Refines coarse) :
    ContextMap (P.proofTheory fine) (P.proofTheory coarse) where
  interface := fun j => j
  term := fun proof => proof
  context := fun context => context
  term_resp := fun related => refines related
  equivariant := fun _ _ => (coarse.setoid _).iseqv.refl _

/-- **Coarsening is hosting exactly when it identifies nothing new.** -/
theorem coarsen_hosting_iff {fine coarse : P.ProofCongruence} (refines : fine.Refines coarse) :
    (P.coarsen refines).Hosting ↔ coarse.Refines fine := by
  rw [P.hosting_iff_static fine (P.coarsen refines) (fun _ _ step => step)]
  exact ⟨fun reflects _ _ _ related => reflects related,
    fun back _ _ _ related => back related⟩

/-- Coarsening is always exhausting: it adds no derived rule. -/
theorem coarsen_exhausting {fine coarse : P.ProofCongruence} (refines : fine.Refines coarse) :
    (P.coarsen refines).Exhausting :=
  fun observer => ⟨observer, fun _ => (coarse.setoid _).iseqv.refl _⟩

/-! ## Finitary signatures -/

/-- A signature is finitary when the premises of every rule are numbered:
each rule instance has an arity, and its positions are the numbers below it. -/
structure Finitary where
  arity : {j : J} → P.Shape PUnit.unit j → Nat
  position : {j : J} → (shape : P.Shape PUnit.unit j) → Fin (arity shape) ≃ P.Position shape

/-- The premises of a rule, in order. -/
def Finitary.positions {P : RuleSignature J} (finitary : P.Finitary) {j : J}
    (shape : P.Shape PUnit.unit j) : List (P.Position shape) :=
  List.ofFn (finitary.position shape)

theorem Finitary.complete {P : RuleSignature J} (finitary : P.Finitary) {j : J}
    (shape : P.Shape PUnit.unit j) (position : P.Position shape) :
    position ∈ finitary.positions shape := by
  rw [Finitary.positions, List.mem_ofFn]
  exact ⟨(finitary.position shape).symm position, (finitary.position shape).apply_symm_apply _⟩

variable {P}

/-- The rule predicate of a finitary signature, in the form the existing
finitary rule closure takes. -/
def Finitary.rules (finitary : P.Finitary) (premises : List J) (conclusion : J) : Prop :=
  ∃ shape : P.Shape PUnit.unit conclusion,
    premises = (finitary.positions shape).map (P.next shape)

/-- **A judgment has a derivation exactly when it is derivable** in the
existing finitary rule closure. -/
theorem nonempty_proof_iff_derives (finitary : P.Finitary) (j : J) :
    Nonempty (P.Proof j) ↔ Mettapedia.Logic.Derives finitary.rules j := by
  constructor
  · rintro ⟨proof⟩
    induction proof using Proof.induction with
    | node shape children ih =>
        refine Mettapedia.Logic.Derives.node _ _ ⟨shape, rfl⟩ ?_
        intro premise member
        obtain ⟨position, _, rfl⟩ := List.mem_map.mp member
        exact ih position
  · intro derives
    refine Mettapedia.Logic.Derives.least (fun j => Nonempty (P.Proof j)) ?_ derives
    rintro premises conclusion ⟨shape, rfl⟩ children
    exact ⟨P.node shape fun position => Classical.choice
      (children _ (List.mem_map.mpr ⟨position, finitary.complete shape position, rfl⟩))⟩

/-- The number of rule nodes of a derivation. -/
noncomputable def size (finitary : P.Finitary) {j : J} (proof : P.Proof j) : Nat :=
  Fix.fold P (carrier := fun _ _ => Nat)
    (fun _ _ layer => 1 + ((finitary.positions layer.1).map layer.2).sum) PUnit.unit j proof

@[simp] theorem size_node (finitary : P.Finitary) {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    size finitary (P.node shape children) =
      1 + ((finitary.positions shape).map fun position => size finitary (children position)).sum :=
  rfl

theorem size_pos (finitary : P.Finitary) {j : J} (proof : P.Proof j) :
    0 < size finitary proof := by
  induction proof using Proof.induction with
  | node shape children _ =>
      rw [size_node]
      omega

end RuleSignature

#print axioms RuleSignature.fill_plug
#print axioms RuleSignature.fill_resp
#print axioms RuleSignature.proofTheory
#print axioms RuleSignature.bisimilar_all
#print axioms RuleSignature.hosting_iff_static
#print axioms RuleSignature.coarsen_hosting_iff
#print axioms RuleSignature.nonempty_proof_iff_derives

end Mettapedia.Logic.HostingStyles
