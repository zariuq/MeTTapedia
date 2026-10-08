import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBoundedFormulaRealization

/-!
# Original-small full-future bounded realizers

Guarded bounded quantification uses literal child receipts. Universal
quantification and implication retain every future context and arrow,
so their carriers remain original-small on an original-small site. The
constructed conversions to and from the ordinary guarded first-order
formula expose exactly why bounded Separation can keep its graph nodes
in the original universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphBoundedRealization

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization (Environment extend moveEnvironment)
open GraphBoundedFormulaRealization (BoundedFormula toFormula)
universe u
variable (D : Type u) [Category.{u} D]

def realize {count : Nat} : BoundedFormula count → (point : D) → Environment D count point → Type u
  | .bottom, _, _ => PEmpty
  | .equal first second, _, environment => Equal (environment first) (environment second)
  | .member child parent, _, environment => Member (environment child) (environment parent)
  | .both left right, point, environment => realize left point environment × realize right point environment
  | .either left right, point, environment => realize left point environment ⊕ realize right point environment
  | .imply left right, point, environment =>
      (target : D) → (arrival : point ⟶ target) →
        realize left target (moveEnvironment D arrival environment) →
          realize right target (moveEnvironment D arrival environment)
  | .allIn parent body, point, environment =>
      (target : D) → (arrival : point ⟶ target) →
        (child : ContextualGraphDiagrams.Child D (move D arrival (environment parent))) →
          realize body target (extend D (childValue D (move D arrival (environment parent)) child)
            (moveEnvironment D arrival environment))
  | .existIn parent body, point, environment =>
      Σ child : ContextualGraphDiagrams.Child D (environment parent),
        realize body point (extend D (childValue D (environment parent) child) environment)

def equalityTransport {count : Nat} (formula : BoundedFormula count) {point : D}
    (first second : Environment D count point) (same : ∀ index, Equal (first index) (second index)) :
    realize D formula point first → realize D formula point second :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal left right => fun proof => (same left).symm.trans (proof.trans (same right))
  | .member child parent => Member.transport (same child) (same parent)
  | .both left right => fun proof =>
      ⟨equalityTransport left first second same proof.1, equalityTransport right first second same proof.2⟩
  | .either left right => fun proof => proof.elim
      (fun data => .inl (equalityTransport left first second same data))
      (fun data => .inr (equalityTransport right first second same data))
  | .imply left right => fun proof target arrival argument =>
      equalityTransport right (moveEnvironment D arrival first) (moveEnvironment D arrival second)
        (fun index => Equal.restrict arrival (same index))
        (proof target arrival (equalityTransport left (moveEnvironment D arrival second)
          (moveEnvironment D arrival first) (fun index => (Equal.restrict arrival (same index)).symm) argument))
  | .allIn parent body => fun proof target arrival child =>
      let matched := ContextualGraphRealizers.Realizer.currentBack (Equal.restrict arrival (same parent)) child
      equalityTransport body
        (extend D (childValue D (move D arrival (first parent)) matched.1) (moveEnvironment D arrival first))
        (extend D (childValue D (move D arrival (second parent)) child) (moveEnvironment D arrival second))
        (Fin.cases matched.2 (fun index => Equal.restrict arrival (same index)))
        (proof target arrival matched.1)
  | .existIn parent body => fun proof =>
      let matched := ContextualGraphRealizers.Realizer.currentForth (same parent) proof.1
      ⟨matched.1, equalityTransport body
        (extend D (childValue D (first parent) proof.1) first)
        (extend D (childValue D (second parent) matched.1) second)
        (Fin.cases matched.2 same) proof.2⟩

def persistence {count : Nat} (formula : BoundedFormula count) {point target : D}
    (arrival : point ⟶ target) (environment : Environment D count point)
    (proof : realize D formula point environment) :
    realize D formula target (moveEnvironment D arrival environment) :=
  match formula with
  | .bottom => proof
  | .equal _ _ => Equal.restrict arrival proof
  | .member _ _ => Member.restrict arrival proof
  | .both left right =>
      ⟨persistence left arrival environment proof.1, persistence right arrival environment proof.2⟩
  | .either left right => proof.elim
      (fun data => .inl (persistence left arrival environment data))
      (fun data => .inr (persistence right arrival environment data))
  | .imply _ _ => fun later tail argument => by
      rw [← ContextualGraphFormulaRealization.moveEnvironment_composition] at argument ⊢
      exact proof later (arrival ≫ tail) argument
  | .allIn parent body => fun later tail child => by
      have same := (environment parent).1.nodes.map_comp_apply arrival tail (environment parent).2
      let original : ContextualGraphDiagrams.Child D (move D (arrival ≫ tail) (environment parent)) :=
        ContextualGraphRealizers.castChild (environment parent).1 same.symm child
      have supplied := proof later (arrival ≫ tail) original
      rw [ContextualGraphFormulaRealization.moveEnvironment_composition] at supplied
      exact supplied
  | .existIn parent body =>
      ⟨moveChild D arrival (environment parent) proof.1,
        (ContextualGraphFormulaRealization.moveEnvironment_extend D arrival
          (childValue D (environment parent) proof.1) environment) ▸
          persistence body arrival _ proof.2⟩

def toFull {count : Nat} (formula : BoundedFormula count) (point : D)
    (environment : Environment D count point) :
    realize D formula point environment →
      ContextualGraphFormulaRealization.realize D (toFormula formula) point environment :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal _ _ => fun proof => ⟨proof⟩
  | .member _ _ => fun proof => ⟨proof⟩
  | .both left right => fun proof =>
      ⟨toFull left point environment proof.1, toFull right point environment proof.2⟩
  | .either left right => fun proof => proof.elim
      (fun data => .inl (toFull left point environment data))
      (fun data => .inr (toFull right point environment data))
  | .imply left right => fun proof target arrival argument =>
      toFull right target (moveEnvironment D arrival environment)
        (proof target arrival (fromFull left target (moveEnvironment D arrival environment) argument))
  | .allIn parent body => fun proof target arrival value later tail member => by
      rw [ContextualGraphFormulaRealization.moveEnvironment_extend,
        ← ContextualGraphFormulaRealization.moveEnvironment_composition] at member ⊢
      let receipt : Member (move D tail value) (move D (arrival ≫ tail) (environment parent)) := member.down
      let supplied := proof later (arrival ≫ tail) receipt.1
      let transported := equalityTransport D body
        (extend D (childValue D (move D (arrival ≫ tail) (environment parent)) receipt.1)
          (moveEnvironment D (arrival ≫ tail) environment))
        (extend D (move D tail value) (moveEnvironment D (arrival ≫ tail) environment))
        (Fin.cases receipt.2.symm (fun index => Equal.refl (move D (arrival ≫ tail) (environment index)))) supplied
      exact toFull body later _ transported
  | .existIn parent body => fun proof =>
      ⟨childValue D (environment parent) proof.1,
        ⟨⟨Member.atChild (environment parent) proof.1⟩,
          toFull body point (extend D (childValue D (environment parent) proof.1) environment) proof.2⟩⟩
where
  fromFull {count : Nat} (formula : BoundedFormula count) (point : D)
      (environment : Environment D count point) :
      ContextualGraphFormulaRealization.realize D (toFormula formula) point environment →
        realize D formula point environment :=
    match formula with
    | .bottom => PEmpty.elim
    | .equal _ _ => fun proof => proof.down
    | .member _ _ => fun proof => proof.down
    | .both left right => fun proof =>
        ⟨fromFull left point environment proof.1, fromFull right point environment proof.2⟩
    | .either left right => fun proof => proof.elim
        (fun data => .inl (fromFull left point environment data))
        (fun data => .inr (fromFull right point environment data))
    | .imply left right => fun proof target arrival argument =>
        fromFull right target (moveEnvironment D arrival environment)
          (proof target arrival (toFull left target (moveEnvironment D arrival environment) argument))
    | .allIn parent body => fun proof target arrival child => by
        let value := childValue D (move D arrival (environment parent)) child
        have current := proof target arrival value target (𝟙 target)
        rw [ContextualGraphFormulaRealization.moveEnvironment_identity] at current
        exact fromFull body target (extend D value (moveEnvironment D arrival environment))
          (current ⟨Member.atChild (move D arrival (environment parent)) child⟩)
    | .existIn parent body => fun proof =>
        let receipt := proof.2.1.down
        ⟨receipt.1, equalityTransport D body
          (extend D proof.1 environment) (extend D (childValue D (environment parent) receipt.1) environment)
          (Fin.cases receipt.2 (fun index => Equal.refl (environment index)))
          (fromFull body point (extend D proof.1 environment) proof.2.2)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphBoundedRealization
