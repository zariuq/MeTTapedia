import Mettapedia.TypeTheory.JudgmentDerivation

/-!
# Presented indexed rule algebras

Equations are imposed on independently generated judgment derivations. The
least rule congruence closes them under the actual premise operations, and
the quotient is an initial algebra among models satisfying those equations.
The interpreter computes on every supplied proof tree and is unique.

This quotient is for rule algebras; it does not itself construct a category
with families or assert independence of different typing certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentEquationInitiality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open JudgmentDerivation

universe u v
variable {S : Signature.{u}}

abbrev Equations (S : Signature.{u}) :=
  {judgment : S.Judgment} → Derivation S judgment → Derivation S judgment → Prop

/-- Every rule position is compared, rather than merely its conclusion. -/
inductive Congruence (E : Equations S) :
    {judgment : S.Judgment} → Derivation S judgment → Derivation S judgment → Prop where
  | equation {j : S.Judgment} {left right : Derivation S j} :
      E left right → Congruence E left right
  | refl {j : S.Judgment} (d : Derivation S j) : Congruence E d d
  | symm {j : S.Judgment} {left right : Derivation S j} :
      Congruence E left right → Congruence E right left
  | trans {j : S.Judgment} {first middle last : Derivation S j} :
      Congruence E first middle → Congruence E middle last → Congruence E first last
  | node {j : S.Judgment} (r : S.Rule j)
      (left right : (p : S.Premise r) → Derivation S (S.hypothesis r p)) :
      (∀ p, Congruence E (left p) (right p)) →
        Congruence E (.node r left) (.node r right)

def derivationSetoid (E : Equations S) (judgment : S.Judgment) :
    Setoid (Derivation S judgment) where
  r := Congruence E
  iseqv := ⟨Congruence.refl, Congruence.symm, Congruence.trans⟩

abbrev Presented (E : Equations S) (judgment : S.Judgment) :=
  Quotient (derivationSetoid E judgment)

def Satisfies (E : Equations S) (A : Algebra.{u, v} S) : Prop :=
  ∀ {j : S.Judgment} {left right : Derivation S j},
    E left right → interpret A left = interpret A right

theorem interpretation_respects_congruence (E : Equations S) (A : Algebra.{u, v} S)
    (laws : Satisfies E A) {j : S.Judgment} {left right : Derivation S j}
    (related : Congruence E left right) : interpret A left = interpret A right := by
  induction related with
  | equation imposed => exact laws imposed
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | node r left right _ ih =>
      simp only [interpret_node]
      congr 1
      funext p
      exact ih p

/-- Quotient operations choose representatives only to construct their
output class. Their independence is established by the rule congruence. -/
noncomputable def presentedAlgebra (E : Equations S) : Algebra.{u, u} S where
  Carrier := Presented E
  conclude r premises := Quotient.mk _
    (.node r (fun p => Quotient.out (premises p)))

/-- The projection preserves the actual rule operations, including all
their indexed premise positions. -/
noncomputable def projection (E : Equations S) :
    Hom (generated S) (presentedAlgebra E) where
  map d := Quotient.mk _ d
  map_conclude := by
    intro j r premises
    apply Quotient.sound
    apply Congruence.node
    intro p
    change Congruence E (premises p)
      (Quotient.out (Quotient.mk (derivationSetoid E _) (premises p)))
    exact Quotient.exact (Quotient.out_eq
      (Quotient.mk (derivationSetoid E _) (premises p))).symm

theorem interpret_presented (E : Equations S) {j : S.Judgment} (d : Derivation S j) :
    interpret (presentedAlgebra E) d = Quotient.mk _ d := by
  have natural := interpret_naturality (projection E) d
  change Quotient.mk (derivationSetoid E _) (interpret (generated S) d) =
    interpret (presentedAlgebra E) d at natural
  rw [interpret_generated] at natural
  exact natural.symm

theorem presented_satisfies (E : Equations S) : Satisfies E (presentedAlgebra E) := by
  intro j left right imposed
  rw [interpret_presented, interpret_presented]
  exact Quotient.sound (Congruence.equation imposed)

/-- Every local semantic model satisfying the presented equations has a
computing interpreter of their quotient. -/
def evaluate (E : Equations S) (A : Algebra.{u, v} S) (laws : Satisfies E A)
    {j : S.Judgment} : Presented E j → A.Carrier j :=
  Quotient.lift (interpret A) (fun _ _ related =>
    interpretation_respects_congruence E A laws related)

@[simp] theorem evaluate_mk (E : Equations S) (A : Algebra.{u, v} S)
    (laws : Satisfies E A) {j : S.Judgment} (d : Derivation S j) :
    evaluate E A laws (Quotient.mk _ d) = interpret A d := rfl

noncomputable def evaluation (E : Equations S) (A : Algebra.{u, v} S)
    (laws : Satisfies E A) : Hom (presentedAlgebra E) A where
  map := evaluate E A laws
  map_conclude := by
    intro j r premises
    change A.conclude r (fun p => interpret A (Quotient.out (premises p))) =
      A.conclude r (fun p => evaluate E A laws (premises p))
    congr 1
    funext p
    exact congrArg (evaluate E A laws) (Quotient.out_eq (premises p))

theorem evaluation_unique (E : Equations S) (A : Algebra.{u, v} S)
    (laws : Satisfies E A) (f : Hom (presentedAlgebra E) A) :
    f = evaluation E A laws := by
  have composite := interpretation_unique A (Hom.comp (projection E) f)
  apply Hom.ext
  intro j value
  induction value using Quotient.inductionOn with
  | h d =>
      exact congrArg (fun h : Hom (generated S) A => h.map d) composite

structure Model (E : Equations S) where
  algebra : Algebra.{u, u} S
  satisfies : Satisfies E algebra

instance modelCategory (E : Equations S) : Category (Model E) where
  Hom A B := JudgmentDerivation.Hom A.algebra B.algebra
  id A := Hom.identity A.algebra
  comp := Hom.comp
  id_comp := by intro A B f; apply Hom.ext; intro j value; rfl
  comp_id := by intro A B f; apply Hom.ext; intro j value; rfl
  assoc := by intro A B D F f g h; apply Hom.ext; intro j value; rfl

noncomputable def presentedModel (E : Equations S) : Model E :=
  ⟨presentedAlgebra E, presented_satisfies E⟩

/-- The initiality includes existence and uniqueness for every qualified
model, not just a canonical self-interpretation. -/
noncomputable def presentedIsInitial (E : Equations S) : IsInitial (presentedModel E) :=
  IsInitial.ofUniqueHom (fun A => evaluation E A.algebra A.satisfies)
    (fun A f => evaluation_unique E A.algebra A.satisfies f)

/-- Equation validity in every local model is exactly the generated
congruence. The reverse direction uses the constructed quotient model. -/
theorem all_models_equal_iff (E : Equations S) {j : S.Judgment}
    (left right : Derivation S j) :
    (∀ (A : Algebra.{u, u} S), Satisfies E A →
      interpret A left = interpret A right) ↔ Congruence E left right := by
  constructor
  · intro allModels
    have equal := allModels (presentedAlgebra E) (presented_satisfies E)
    rw [interpret_presented, interpret_presented] at equal
    exact Quotient.exact equal
  · intro related A laws
    exact interpretation_respects_congruence E A laws related

/-- A semantic readout distinguishing two supplied proofs disproves their
identification by the presentation's equations. -/
theorem separated_not_congruent (E : Equations S) (A : Algebra.{u, v} S)
    (laws : Satisfies E A) {j : S.Judgment} {left right : Derivation S j}
    (separated : interpret A left ≠ interpret A right) :
    ¬ Congruence E left right :=
  fun related => separated (interpretation_respects_congruence E A laws related)

/-- Any congruence sound for the generators and all rules contains the
generated congruence. -/
theorem congruence_least (E : Equations S)
    (R : {j : S.Judgment} → Derivation S j → Derivation S j → Prop)
    (equations : ∀ {j} {left right : Derivation S j}, E left right → R left right)
    (reflexive : ∀ {j} (d : Derivation S j), R d d)
    (symmetric : ∀ {j} {left right : Derivation S j}, R left right → R right left)
    (transitive : ∀ {j} {first middle last : Derivation S j},
      R first middle → R middle last → R first last)
    (rules : ∀ {j} (r : S.Rule j)
      (left right : (p : S.Premise r) → Derivation S (S.hypothesis r p)),
      (∀ p, R (left p) (right p)) → R (.node r left) (.node r right))
    {j : S.Judgment} {left right : Derivation S j} :
    Congruence E left right → R left right := by
  intro related
  induction related with
  | equation imposed => exact equations imposed
  | refl d => exact reflexive d
  | symm _ ih => exact symmetric ih
  | trans _ _ first second => exact transitive first second
  | node r left right _ ih => exact rules r left right ih

end Mettapedia.TypeTheory.JudgmentEquationInitiality
