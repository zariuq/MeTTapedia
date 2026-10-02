import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Logic.EliminatorObservers
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ProofRelevance

/-!
# Quotients as observer bubbles

Observational type theory plans quotients "as abstract datatypes, allowing you
access to the element of the underlying set only if you can prove that you
respect the equivalence", with observational equality on the quotient reducing
to the given equivalence (Altenkirch, McBride and Swierstra, PLPV 2007, §7).
This module proves that this is the bubble whose admissible observers are the
`R`-respecting ones, in both observer frameworks of the development.

**Typed observation relation.**  An observer into a sort observed by equality is
admissible for `R` exactly when it respects `R` (`respects_iff_admissible`, from
`quote_admissible_iff`); exactly when it factors through the quotient map, the
quotient's only eliminator (`respects_iff_factors`); and the equivalence of all
admissible observers is the equivalence closure of `R`
(`respectingEquiv_iff_eqvGen`), which is `R` itself when `R` is an equivalence.

**Saturated relative equivalence.**  With terms `X`, nothing reducing, contexts
the endofunctions of `X` and atoms the `R`-closed predicates, the class of
contexts mapping `R`-related points to `R`-equivalent points has the
equivalence closure of `R` as its relative equivalence
(`relEquiv_congruences_iff`), and it is the class determined by that
equivalence (`congruences_determined`).  An endofunction that does not respect
`R` separates an `R`-related pair once adjoined (`parity_not_relEquiv_sup_half`).

**Propositions and proofs as quotients.**  Proof irrelevance is the quotient of
proofs by the total relation: the proof inspector of `⊤ ∨ ⊤` is not admissible
for it (`inspect_not_admissible`).  Propositional extensionality is the quotient
of proposition codes by logical equivalence: truth is admissible
(`truth_admissible`), while the code observer that recognises `⊤` is not
(`isTopCode_not_admissible`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.QuotientObservers

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.TypedObservation

universe u

/-! ## Respecting observers in the typed observation relation -/

section Respecting

variable {X : Type u} (R : X → X → Prop)

/-- An observer respects `R` when it is constant on `R`-related points. -/
def Respects {Y : Type u} (observer : X → Y) : Prop :=
  ∀ x x', R x x' → observer x = observer x'

/-- **Admissible means respecting**: an observer into a sort observed by
equality is admissible for `R` in the typed observation relation exactly when
it respects `R`. -/
theorem respects_iff_admissible {Y : Type u} (observer : X → Y) :
    Respects R observer ↔
      Admissible (Carrier := fun _ : Unit => Y) R (equalityChoice (fun _ : Unit => Y))
        (.arrow .proc (.ground ())) observer :=
  (quote_admissible_iff R (equalityChoice (fun _ : Unit => Y)) (fun _ _ => Iff.rfl)
    observer).symm

/-- **Respecting means factoring through the quotient**, whose eliminator is the
only access to the underlying points. -/
theorem respects_iff_factors {Y : Type u} (observer : X → Y) :
    Respects R observer ↔ Factors (Quot.mk R) observer := by
  constructor
  · intro respects
    exact ⟨Quot.lift observer respects, fun _ => rfl⟩
  · rintro ⟨recover, recovers⟩ x x' related
    rw [← recovers x, ← recovers x', Quot.sound related]

/-- The equivalence of all respecting observers. -/
def RespectingEquiv (x x' : X) : Prop :=
  ∀ (Y : Type u) (observer : X → Y), Respects R observer → observer x = observer x'

theorem Respects.eqvGen {Y : Type u} {observer : X → Y} (respects : Respects R observer)
    {x x' : X} (related : Relation.EqvGen R x x') : observer x = observer x' := by
  induction related with
  | rel _ _ step => exact respects _ _ step
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **The equality of the quotient bubble is the equivalence closure of `R`.** -/
theorem respectingEquiv_iff_eqvGen (x x' : X) :
    RespectingEquiv R x x' ↔ Relation.EqvGen R x x' := by
  constructor
  · intro agree
    exact Quot.eqvGen_exact (agree (Quot R) (Quot.mk R) fun _ _ related => Quot.sound related)
  · intro related _ _ respects
    exact respects.eqvGen R related

/-- **For an equivalence relation, observational equality on the quotient
reduces to the relation.** -/
theorem respectingEquiv_iff_of_equivalence (equivalence : Equivalence R) (x x' : X) :
    RespectingEquiv R x x' ↔ R x x' :=
  (respectingEquiv_iff_eqvGen R x x').trans equivalence.eqvGen_iff

end Respecting

/-! ## The quotient bubble in the saturated framework -/

section Bubble

variable (X : Type u)

/-- Points of `X` up to identity; nothing reduces. -/
def pointGSLT : GSLT where
  Term := X
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ step => step.elim
  rewrites_resp_right := fun step _ => step.elim

theorem pointGSLT_inert (source target : X) : ¬ (pointGSLT X).Step source target :=
  fun step => step

/-- Contexts are the endofunctions of `X`. -/
def endoRules : ContextualRules (pointGSLT X) where
  Context := X → X
  identity := id
  compose outer inner := outer ∘ inner
  plug context x := context x
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp context _ _ equal := congrArg context equal
  Rule := Empty
  fires rule _ _ := rule.elim
  fires_resp_left := by intro rule; exact rule.elim
  fires_resp_right := by intro rule; exact rule.elim
  fires_step := by intro rule; exact rule.elim

variable {X} (R : X → X → Prop)

/-- Atoms: the predicates closed under `R`. -/
def closedPredicates : ContextualRules.Observations.{u} (pointGSLT X) where
  Atom := {predicate : X → Prop // ∀ x x', R x x' → (predicate x ↔ predicate x')}
  observes predicate x := predicate.1 x
  observes_resp _ _ _ equal := by
    change _ = _ at equal
    rw [equal]

theorem EqvGen.map_of_rel {context : X → X}
    (preserves : ∀ x x', R x x' → Relation.EqvGen R (context x) (context x')) {x x' : X}
    (related : Relation.EqvGen R x x') : Relation.EqvGen R (context x) (context x') := by
  induction related with
  | rel _ _ step => exact preserves _ _ step
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **The congruences of `R`**: contexts mapping `R`-related points to
`R`-equivalent points. -/
def congruences : AdmissibleClass (endoRules X) where
  Admissible context := ∀ x x', R x x' → Relation.EqvGen R (context x) (context x')
  identity_mem := fun _ _ related => .rel _ _ related
  compose_mem := fun outerPreserves innerPreserves x x' related =>
    EqvGen.map_of_rel R outerPreserves (innerPreserves x x' related)

theorem closedPredicate_eqvGen {predicate : X → Prop}
    (closed : ∀ x x', R x x' → (predicate x ↔ predicate x')) {x x' : X}
    (related : Relation.EqvGen R x x') : predicate x ↔ predicate x' := by
  induction related with
  | rel _ _ step => exact closed _ _ step
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **The relative equivalence of the congruences is the equivalence closure of
`R`.** -/
theorem relEquiv_congruences_iff (x x' : X) :
    (congruences R).RelEquiv (closedPredicates R) x x' ↔ Relation.EqvGen R x x' := by
  refine (EliminatorObservers.relEquiv_iff_of_inert (pointGSLT_inert X) (congruences R)
    (closedPredicates R) x x').trans ?_
  constructor
  · intro agree
    have atom := agree id (congruences R).identity_mem
      ⟨fun y => Relation.EqvGen R x y, fun y y' related =>
        ⟨fun toY => .trans _ _ _ toY (.rel _ _ related),
          fun toY' => .trans _ _ _ toY' (.symm _ _ (.rel _ _ related))⟩⟩
    exact atom.mp (.refl x)
  · intro related context admissible predicate
    exact closedPredicate_eqvGen R predicate.2 (EqvGen.map_of_rel R admissible related)

/-- **The quotient bubble is determined by its equality**: its admissible
contexts are exactly the contexts preserving it. -/
theorem congruences_determined :
    (congruences R).determined (closedPredicates R) = congruences R := by
  rw [AdmissibleClass.determined_eq_self_iff]
  intro context preserves x x' related
  have image := preserves ((relEquiv_congruences_iff R x x').mpr (.rel _ _ related))
  exact (relEquiv_congruences_iff R _ _).mp image

end Bubble

/-! ## Control: an observer that does not respect the relation -/

namespace Parity

/-- Having the same parity. -/
def SameParity (m n : ℕ) : Prop := m % 2 = n % 2

/-- Parity respects the relation ... -/
theorem parity_respects : Respects SameParity (fun n : ℕ => n % 2) := fun _ _ same => same

/-- ... while halving does not: it separates `0` and `2`. -/
theorem half_not_respects : ¬ Respects SameParity (fun n : ℕ => n / 2) := fun respects =>
  absurd (respects 0 2 rfl) (by decide)

theorem half_not_admissible :
    ¬ Admissible (Carrier := fun _ : Unit => ℕ) SameParity (equalityChoice (fun _ : Unit => ℕ))
      (.arrow .proc (.ground ())) (fun n : ℕ => n / 2) := fun admissible =>
  half_not_respects ((respects_iff_admissible SameParity _).mpr admissible)

/-- **Adjoining halving to the congruences of parity separates `0` from `2`.** -/
theorem parity_not_relEquiv_sup_half :
    ¬ (congruences SameParity ⊔
        AdmissibleClass.generatedBy {(fun n : ℕ => n / 2 : ℕ → ℕ)}).RelEquiv
      (closedPredicates SameParity) (0 : ℕ) (2 : ℕ) := by
  refine AdmissibleClass.not_relEquiv_sup_of_not_preserved (closedPredicates SameParity)
    (congruences SameParity) (Set.mem_singleton _) ?_
  change ¬ (congruences SameParity).RelEquiv (closedPredicates SameParity) (0 : ℕ) (1 : ℕ)
  rw [relEquiv_congruences_iff]
  intro related
  exact absurd (Respects.eqvGen SameParity parity_respects related) (by decide)

theorem parity_relEquiv :
    (congruences SameParity).RelEquiv (closedPredicates SameParity) (0 : ℕ) (2 : ℕ) :=
  (relEquiv_congruences_iff SameParity 0 2).mpr (.rel _ _ rfl)

end Parity

/-! ## Propositions and proofs as quotients -/

section Propositions

open Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- The total relation on proofs: proof irrelevance identifies all proofs. -/
def AllProofs (P : PropCode) (_ _ : P.Proof) : Prop := True

/-- **The proof inspector is not admissible for proof irrelevance.** -/
theorem inspect_not_admissible :
    ¬ Admissible (Carrier := fun _ : Unit => Bool) (AllProofs Disjunction.twoProofs)
      (equalityChoice (fun _ : Unit => Bool)) (.arrow .proc (.ground ())) Disjunction.inspect :=
  quote_not_admissible (AllProofs Disjunction.twoProofs) (equalityChoice (fun _ : Unit => Bool))
    (fun _ _ => Iff.rfl) Disjunction.inspect (first := Disjunction.leftProof)
    (second := Disjunction.rightProof) trivial Disjunction.inspect_separates

/-- In the fragment, every observer of proofs is admissible for proof
irrelevance. -/
theorem admissible_of_inFragment {P : PropCode} (inFragment : P.InFragment) (observer : P.Proof → Bool) :
    Admissible (Carrier := fun _ : Unit => Bool) (AllProofs P)
      (equalityChoice (fun _ : Unit => Bool)) (.arrow .proc (.ground ())) observer :=
  (quote_admissible_iff (AllProofs P) (equalityChoice (fun _ : Unit => Bool)) (fun _ _ => Iff.rfl)
    observer).mpr fun first second _ =>
      congrArg observer ((PropCode.proof_subsingleton inFragment).elim first second)

/-- Logical equivalence of proposition codes. -/
def LogicallyEquivalent (P Q : PropCode) : Prop :=
  Nonempty (P.Proof → Q.Proof) ∧ Nonempty (Q.Proof → P.Proof)

/-- **Truth is admissible for logical equivalence.** -/
theorem truth_admissible :
    Admissible (Carrier := fun _ : Unit => Prop) LogicallyEquivalent
      (equalityChoice (fun _ : Unit => Prop)) (.arrow .proc (.ground ()))
      (fun P : PropCode => Nonempty P.Proof) :=
  (quote_admissible_iff LogicallyEquivalent (equalityChoice (fun _ : Unit => Prop))
    (fun _ _ => Iff.rfl) _).mpr fun _ _ ⟨⟨forward⟩, ⟨backward⟩⟩ =>
      propext ⟨fun ⟨proof⟩ => ⟨forward proof⟩, fun ⟨proof⟩ => ⟨backward proof⟩⟩

/-- A code observer on propositions: does the code read `⊤`? -/
def isTopCode : PropCode → Bool
  | .top => true
  | _ => false

/-- **Recognising `⊤` by its code is not admissible for logical
equivalence**: it separates `⊤` from `⊤ ∧ ⊤`. -/
theorem isTopCode_not_admissible :
    ¬ Admissible (Carrier := fun _ : Unit => Bool) LogicallyEquivalent
      (equalityChoice (fun _ : Unit => Bool)) (.arrow .proc (.ground ())) isTopCode :=
  quote_not_admissible LogicallyEquivalent (equalityChoice (fun _ : Unit => Bool))
    (fun _ _ => Iff.rfl) isTopCode (first := .top) (second := .and .top .top)
    ⟨⟨fun proof => (proof, proof)⟩, ⟨fun proof => proof.1⟩⟩ Bool.noConfusion

end Propositions

end Mettapedia.GSLT.QuotientObservers
