import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization

/-!
# Small bounded formula realizers and graph separation

Bounded quantifiers range over actual child receipts. All their realizer
types remain at the graph-node bound. Each bounded formula embeds into
the ordinary first-order syntax; realization maps in both directions
connect the bounded interpretation to its guarded first-order formula.
The maps use computed graph-equality transport, including duplicate
receipts, rather than selecting witnesses from propositions.

Separation uses the small dependent sum of a child receipt and its bounded
formula realizer. Thus the separated graph has the original graph bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBoundedFormulaRealization

open GraphBisimulationRealizers GraphSetRealization GraphFormulaRealization

universe u

inductive BoundedFormula : Nat → Type where
  | bottom {count : Nat} : BoundedFormula count
  | equal {count : Nat} (first second : Fin count) : BoundedFormula count
  | member {count : Nat} (child parent : Fin count) : BoundedFormula count
  | both {count : Nat} (left right : BoundedFormula count) : BoundedFormula count
  | either {count : Nat} (left right : BoundedFormula count) : BoundedFormula count
  | imply {count : Nat} (left right : BoundedFormula count) : BoundedFormula count
  | allIn {count : Nat} (parent : Fin count) (body : BoundedFormula (count+1)) : BoundedFormula count
  | existIn {count : Nat} (parent : Fin count) (body : BoundedFormula (count+1)) : BoundedFormula count

def toFormula {count : Nat} : BoundedFormula count → Formula count
  | .bottom => .bottom
  | .equal first second => .equal first second
  | .member child parent => .member child parent
  | .both left right => .both (toFormula left) (toFormula right)
  | .either left right => .either (toFormula left) (toFormula right)
  | .imply left right => .imply (toFormula left) (toFormula right)
  | .allIn parent body => .all (.imply (.member 0 parent.succ) (toFormula body))
  | .existIn parent body => .exist (.both (.member 0 parent.succ) (toFormula body))

def realize {count : Nat} : BoundedFormula count → Environment.{u} count → Type u
  | .bottom, _ => PEmpty
  | .equal first second, environment => Equal (environment first) (environment second)
  | .member child parent, environment => Member (environment child) (environment parent)
  | .both left right, environment => realize left environment × realize right environment
  | .either left right, environment => realize left environment ⊕ realize right environment
  | .imply left right, environment => realize left environment → realize right environment
  | .allIn parent body, environment => (child : Child (environment parent).edge (environment parent).point) →
      realize body (extend ((environment parent).repoint child.val) environment)
  | .existIn parent body, environment => Σ child : Child (environment parent).edge (environment parent).point,
      realize body (extend ((environment parent).repoint child.val) environment)

/-- A bounded formula transports actual matching receipts at its quantified
parent as well as the other free variables. -/
def transport {count : Nat} (formula : BoundedFormula count) (first second : Environment.{u} count)
    (same : ∀ index, Equal (first index) (second index)) :
    realize formula first → realize formula second :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal left right => fun proof => (same left).symm.trans (proof.trans (same right))
  | .member child parent => Member.transport (same child) (same parent)
  | .both left right => fun proof =>
      ⟨transport left first second same proof.1, transport right first second same proof.2⟩
  | .either left right => fun proof =>
      match proof with
      | .inl value => .inl (transport left first second same value)
      | .inr value => .inr (transport right first second same value)
  | .imply left right => fun proof argument =>
      transport right first second same
        (proof (transport left second first (fun index => (same index).symm) argument))
  | .allIn parent body => fun proof target =>
      let matched := (same parent).out.2 target
      transport body (extend ((first parent).repoint matched.1.val) first)
        (extend ((second parent).repoint target.val) second)
        (Fin.cases (pointed matched.2) same) (proof matched.1)
  | .existIn parent body => fun proof =>
      let matched := (same parent).out.1 proof.1
      ⟨matched.1, transport body (extend ((first parent).repoint proof.1.val) first)
        (extend ((second parent).repoint matched.1.val) second)
        (Fin.cases (pointed matched.2) same) proof.2⟩

/-- A bounded realizer computes a realizer of its guarded first-order formula. -/
def toFull {count : Nat} (formula : BoundedFormula count) (environment : Environment.{u} count) :
    realize formula environment → GraphFormulaRealization.realize (toFormula formula) environment :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal _ _ => fun proof => ⟨proof⟩
  | .member _ _ => fun proof => ⟨proof⟩
  | .both left right => fun proof =>
      ⟨toFull left environment proof.1, toFull right environment proof.2⟩
  | .either left right => fun proof =>
      match proof with
      | .inl value => .inl (toFull left environment value)
      | .inr value => .inr (toFull right environment value)
  | .imply left right => fun proof argument =>
      toFull right environment (proof (fromFull left environment argument))
  | .allIn parent body => fun proof value member =>
      let receipt := member.down
      let bodyProof := transport body
        (extend ((environment parent).repoint receipt.1.val) environment)
        (extend value environment)
        (Fin.cases receipt.2.symm (fun index => Equal.refl (environment index))) (proof receipt.1)
      toFull body (extend value environment) bodyProof
  | .existIn parent body => fun proof =>
      ⟨(environment parent).repoint proof.1.val,
        ⟨⟨Member.atChild (environment parent) proof.1⟩,
          toFull body (extend ((environment parent).repoint proof.1.val) environment) proof.2⟩⟩
where
  /-- Full guarded realizers compute actual bounded receipts. -/
  fromFull {count : Nat} (formula : BoundedFormula count) (environment : Environment.{u} count) :
      GraphFormulaRealization.realize (toFormula formula) environment → realize formula environment :=
    match formula with
    | .bottom => PEmpty.elim
    | .equal _ _ => fun proof => proof.down
    | .member _ _ => fun proof => proof.down
    | .both left right => fun proof =>
        ⟨fromFull left environment proof.1, fromFull right environment proof.2⟩
    | .either left right => fun proof =>
        match proof with
        | .inl value => .inl (fromFull left environment value)
        | .inr value => .inr (fromFull right environment value)
    | .imply left right => fun proof argument =>
        fromFull right environment (proof (toFull left environment argument))
    | .allIn parent body => fun proof child =>
        fromFull body (extend ((environment parent).repoint child.val) environment)
          (proof ((environment parent).repoint child.val) ⟨Member.atChild (environment parent) child⟩)
    | .existIn parent body => fun proof =>
        let receipt := proof.2.1.down
        ⟨receipt.1, transport body (extend proof.1 environment)
          (extend ((environment parent).repoint receipt.1.val) environment)
          (Fin.cases receipt.2 (fun index => Equal.refl (environment index)))
          (fromFull body (extend proof.1 environment) proof.2.2)⟩

/-- The child and its bounded proof form an original-small index carrier. -/
abbrev SeparationIndex {count : Nat} (formula : BoundedFormula (count+1))
    (environment : Environment.{u} count) (parent : Graph.{u}) : Type u :=
  Σ child : Child parent.edge parent.point, realize formula (extend (parent.repoint child.val) environment)

def separation {count : Nat} (formula : BoundedFormula (count+1))
    (environment : Environment.{u} count) (parent : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun receipt : SeparationIndex formula environment parent =>
    parent.repoint receipt.1.val)

def separationIntro {count : Nat} (formula : BoundedFormula (count+1))
    (environment : Environment.{u} count) {value parent : Graph.{u}}
    (member : Member value parent) (proof : realize formula (extend value environment)) :
    Member value (separation formula environment parent) :=
  Sup.intro _
    ⟨member.1, transport formula (extend value environment)
      (extend (parent.repoint member.1.val) environment)
      (Fin.cases member.2 (fun index => Equal.refl (environment index))) proof⟩ member.2

def separationEliminate {count : Nat} (formula : BoundedFormula (count+1))
    (environment : Environment.{u} count) {value parent : Graph.{u}}
    (proof : Member value (separation formula environment parent)) :
    Member value parent × realize formula (extend value environment) :=
  let decoded := Sup.eliminate _ proof
  ⟨⟨decoded.1.1, decoded.2⟩,
    transport formula (extend (parent.repoint decoded.1.1.val) environment)
      (extend value environment)
      (Fin.cases decoded.2.symm (fun index => Equal.refl (environment index))) decoded.1.2⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBoundedFormulaRealization
