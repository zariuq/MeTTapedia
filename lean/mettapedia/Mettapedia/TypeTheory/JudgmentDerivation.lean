import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Generated indexed judgments and their rule-algebra interpretation

A rule has an independently supplied conclusion and indexed premises. The
generated object retains its rule and every premise derivation, including
different occurrences of the same judgment. Interpretation uses only the
local rule operations of the target algebra. Existence, computation and
uniqueness are derived from the generated trees.

This is initiality of an indexed rule algebra. A classifying category with
families additionally requires substitution, comprehension and the relevant
equations; none of those obligations is identified with this theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentDerivation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w x

/-- Premise positions belong to the rule, even when their judgments agree. -/
structure Signature where
  Judgment : Type u
  Rule : Judgment → Type u
  Premise : {judgment : Judgment} → Rule judgment → Type u
  hypothesis : {judgment : Judgment} → (rule : Rule judgment) →
    Premise rule → Judgment

/-- Independently generated, proof-relevant derivations. -/
inductive Derivation (S : Signature.{u}) : S.Judgment → Type u where
  | node {judgment : S.Judgment} (rule : S.Rule judgment)
      (premises : (position : S.Premise rule) →
        Derivation S (S.hypothesis rule position)) : Derivation S judgment

/-- A model supplies local operations, rather than an interpretation or a
global soundness claim as a field. -/
structure Algebra (S : Signature.{u}) where
  Carrier : S.Judgment → Type v
  conclude : {judgment : S.Judgment} → (rule : S.Rule judgment) →
    ((position : S.Premise rule) → Carrier (S.hypothesis rule position)) →
      Carrier judgment

variable {S : Signature.{u}}

abbrev generated (S : Signature.{u}) : Algebra.{u, u} S where
  Carrier := Derivation S
  conclude := Derivation.node

/-- Interpretation is recursive on the supplied derivation, not on a
proof-irrelevant assertion that a judgment is derivable. -/
def interpret (A : Algebra.{u, v} S) {judgment : S.Judgment} :
    Derivation S judgment → A.Carrier judgment
  | .node rule premises => A.conclude rule (fun position => interpret A (premises position))

@[simp] theorem interpret_node (A : Algebra.{u, v} S)
    {judgment : S.Judgment} (rule : S.Rule judgment)
    (premises : (position : S.Premise rule) → Derivation S (S.hypothesis rule position)) :
    interpret A (.node rule premises) =
      A.conclude rule (fun position => interpret A (premises position)) := rfl

structure Hom (A : Algebra.{u, v} S) (B : Algebra.{u, w} S) where
  map : {judgment : S.Judgment} → A.Carrier judgment → B.Carrier judgment
  map_conclude : ∀ {judgment : S.Judgment} (rule : S.Rule judgment)
      (premises : (position : S.Premise rule) → A.Carrier (S.hypothesis rule position)),
    map (A.conclude rule premises) = B.conclude rule (fun position => map (premises position))

namespace Hom

@[ext] theorem ext {A : Algebra.{u, v} S} {B : Algebra.{u, w} S} {f g : Hom A B}
    (same : ∀ {judgment : S.Judgment} (value : A.Carrier judgment),
      f.map value = g.map value) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have maps : @f = @g := by funext judgment value; exact same value
      cases maps
      rfl

def identity (A : Algebra.{u, v} S) : Hom A A where
  map := id
  map_conclude := fun _ _ => rfl

def comp {A : Algebra.{u, v} S} {B : Algebra.{u, w} S}
    {D : Algebra.{u, x} S} (f : Hom A B) (g : Hom B D) : Hom A D where
  map := fun value => g.map (f.map value)
  map_conclude := by
    intro judgment rule premises
    rw [f.map_conclude, g.map_conclude]

end Hom

/-- The generated interpreter preserves every rule operation. -/
def interpretation (A : Algebra.{u, v} S) : Hom (generated S) A where
  map := interpret A
  map_conclude := interpret_node A

theorem interpretation_unique (A : Algebra.{u, v} S) (f : Hom (generated S) A) :
    f = interpretation A := by
  apply Hom.ext
  intro judgment derivation
  induction derivation with
  | node rule premises ih =>
      change f.map ((generated S).conclude rule premises) =
        A.conclude rule (fun position => interpret A (premises position))
      rw [f.map_conclude]
      congr 1
      funext position
      exact ih position

@[simp] theorem interpret_generated {judgment : S.Judgment} (d : Derivation S judgment) :
    interpret (generated S) d = d := by
  exact congrArg (fun f : Hom (generated S) (generated S) => f.map d)
    (interpretation_unique (generated S) (Hom.identity (generated S))).symm

/-- Arbitrary target universes are allowed in the unique interpreter. -/
@[instance_reducible] def uniqueInterpretation (A : Algebra.{u, v} S) :
    Unique (Hom (generated S) A) where
  default := interpretation A
  uniq := interpretation_unique A

/-- A rule homomorphism transports the interpreted evidence exactly. -/
theorem interpret_naturality {A : Algebra.{u, v} S} {B : Algebra.{u, w} S}
    (f : Hom A B) {judgment : S.Judgment} (derivation : Derivation S judgment) :
    f.map (interpret A derivation) = interpret B derivation := by
  induction derivation with
  | node rule premises ih =>
      rw [interpret_node, f.map_conclude, interpret_node]
      congr 1
      funext position
      exact ih position

instance algebraCategory (S : Signature.{u}) : Category (Algebra.{u, u} S) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := by intro A B f; apply Hom.ext; intro judgment value; rfl
  comp_id := by intro A B f; apply Hom.ext; intro judgment value; rfl
  assoc := by intro A B D E f g h; apply Hom.ext; intro judgment value; rfl

/-- The actual generated algebra is initial in its category of models. -/
def generatedIsInitial (S : Signature.{u}) : IsInitial (generated S) :=
  IsInitial.ofUniqueHom (interpretation) (fun A f => interpretation_unique A f)

/-- Translating a rule presentation explicitly maps its premise positions.
It can reorder, duplicate or omit premises. The map alone is therefore not
a theorem that every source occurrence survives translation. -/
structure SignatureMap (S T : Signature.{u}) where
  judgment : S.Judgment → T.Judgment
  rule : {j : S.Judgment} → S.Rule j → T.Rule (judgment j)
  position : {j : S.Judgment} → (r : S.Rule j) → T.Premise (rule r) → S.Premise r
  hypothesis : ∀ {j : S.Judgment} (r : S.Rule j) (p : T.Premise (rule r)),
    judgment (S.hypothesis r (position r p)) = T.hypothesis (rule r) p

namespace SignatureMap

variable {T : Signature.{u}}

def pullback (F : SignatureMap S T) (A : Algebra.{u, v} T) : Algebra.{u, v} S where
  Carrier j := A.Carrier (F.judgment j)
  conclude r premises := A.conclude (F.rule r) (fun p =>
    cast (congrArg A.Carrier (F.hypothesis r p)) (premises (F.position r p)))

/-- Translate supplied proofs by recursive rule application, retaining
explicit transports of every dependent premise judgment. -/
def translate (F : SignatureMap S T) {j : S.Judgment} :
    Derivation S j → Derivation T (F.judgment j) :=
  interpret (F.pullback (generated T))

theorem interpret_translate (F : SignatureMap S T) (A : Algebra.{u, v} T)
    {j : S.Judgment} (d : Derivation S j) :
    interpret A (F.translate d) = interpret (F.pullback A) d := by
  induction d with
  | node r premises ih =>
      change A.conclude (F.rule r)
          (fun p => interpret A (cast
            (congrArg (Derivation T) (F.hypothesis r p))
            (F.translate (premises (F.position r p))))) =
        A.conclude (F.rule r) (fun p =>
          cast (congrArg A.Carrier (F.hypothesis r p))
            (interpret (F.pullback A) (premises (F.position r p))))
      congr 1
      funext p
      have transport : ∀ {x y : T.Judgment} (same : x = y) (tree : Derivation T x),
          interpret A (cast (congrArg (Derivation T) same) tree) =
            cast (congrArg A.Carrier same) (interpret A tree) := by
        intro x y same tree
        cases same
        rfl
      rw [transport (F.hypothesis r p), ih (F.position r p)]

end SignatureMap

end Mettapedia.TypeTheory.JudgmentDerivation
