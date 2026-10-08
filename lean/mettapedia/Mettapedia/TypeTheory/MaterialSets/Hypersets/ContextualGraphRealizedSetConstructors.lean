import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGenerators

/-!
# Set constructors in the varying realized graph universe

Enumeration retains literal small indices. Union additionally retains
all future source contexts and their two membership occurrences; it does
not freeze the members visible at construction time. Every constructor
is an actual original-small diagram in the same untyped value carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetConstructors

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D]

section Enumeration
variable {point : D} {Index : Type u} (family : Index → Value D point)

def enumeration : Value D point :=
  ContextualGraphGenerators.root (fun _ : Index => point) (fun _ => 𝟙 point) family (𝟙 point)

def enumerationRoot {target : D} (path : point ⟶ target) : Value D target :=
  ContextualGraphGenerators.root (fun _ : Index => point) (fun _ => 𝟙 point) family path

theorem enumeration_move {target : D} (path : point ⟶ target) :
    move D path (enumeration family) = enumerationRoot family path :=
  congrArg (ContextualGraphGenerators.root (fun _ : Index => point) (fun _ => 𝟙 point) family)
    (Category.id_comp path)

def enumerationIntro {target : D} (path : point ⟶ target) (index : Index)
    {value : Value D target} (same : Equal value (move D path (family index))) :
    Member value (move D path (enumeration family)) :=
  Member.transportParent (Equal.ofEq (enumeration_move family path).symm)
    (Member.transportChild same.symm
      (ContextualGraphGenerators.rootIntro (fun _ : Index => point) (fun _ => 𝟙 point)
        family path index path (Category.id_comp path)))

def enumerationEliminate {target : D} (path : point ⟶ target) {value : Value D target}
    (proof : Member value (move D path (enumeration family))) :
    Σ index : Index, Equal value (move D path (family index)) := by
  let current := Member.transportParent (Equal.ofEq (enumeration_move family path)) proof
  let decoded := ContextualGraphGenerators.rootDecode (fun _ : Index => point) (fun _ => 𝟙 point)
    family path current.1
  have same : decoded.2.1 = path := by simpa using decoded.2.2.1.down
  refine ⟨decoded.1, ?_⟩
  have response := current.2.trans decoded.2.2.2
  rw [same] at response
  exact response

end Enumeration

def empty (point : D) : Value D point :=
  enumeration (fun impossible : PEmpty.{u+1} => PEmpty.elim impossible)

def emptyEliminate {point target : D} (path : point ⟶ target) {value : Value D target}
    (proof : Member value (move D path (empty point))) : PEmpty.{u+1} :=
  PEmpty.elim (enumerationEliminate _ path proof).1

def pair {point : D} (first second : Value D point) : Value D point :=
  enumeration (fun index : ULift.{u} Bool => if index.down then second else first)

def pairFirst {point target : D} (path : point ⟶ target) (first second : Value D point) :
    Member (move D path first) (move D path (pair first second)) :=
  enumerationIntro _ path ⟨false⟩ (Equal.refl _)

def pairSecond {point target : D} (path : point ⟶ target) (first second : Value D point) :
    Member (move D path second) (move D path (pair first second)) :=
  enumerationIntro _ path ⟨true⟩ (Equal.refl _)

def pairEliminate {point target : D} (path : point ⟶ target) {first second : Value D point}
    {value : Value D target} (proof : Member value (move D path (pair first second))) :
    Equal value (move D path first) ⊕ Equal value (move D path second) :=
  match enumerationEliminate _ path proof with
  | ⟨⟨false⟩, same⟩ => .inl same
  | ⟨⟨true⟩, same⟩ => .inr same

def emptyReindex {point target : D} (path : point ⟶ target) :
    Equal (move D path (empty point)) (empty target) :=
  extensionality
    (fun _ tail _ proof => PEmpty.elim (emptyEliminate (path ≫ tail)
      (Member.transportParent (Equal.ofEq (move_composition D path tail (empty point)).symm) proof)))
    (fun _ tail _ proof => PEmpty.elim (emptyEliminate tail proof))

def pairCongruence {point : D} {first first' second second' : Value D point}
    (left : Equal first first') (right : Equal second second') :
    Equal (pair first second) (pair first' second') :=
  extensionality
    (fun _ path _ proof => match pairEliminate path proof with
      | .inl same => Member.transportChild (same.trans (left.restrict path)).symm (pairFirst path first' second')
      | .inr same => Member.transportChild (same.trans (right.restrict path)).symm (pairSecond path first' second'))
    (fun _ path _ proof => match pairEliminate path proof with
      | .inl same => Member.transportChild (same.trans (left.restrict path).symm).symm (pairFirst path first second)
      | .inr same => Member.transportChild (same.trans (right.restrict path).symm).symm (pairSecond path first second))

def pairReindex {point target : D} (path : point ⟶ target) (first second : Value D point) :
    Equal (move D path (pair first second)) (pair (move D path first) (move D path second)) :=
  extensionality
    (fun _ tail _ proof =>
      let normalized := Member.transportParent (Equal.ofEq (move_composition D path tail (pair first second)).symm) proof
      match pairEliminate (path ≫ tail) normalized with
      | .inl same => Member.transportChild (same.trans (Equal.ofEq (move_composition D path tail first))).symm
          (pairFirst tail (move D path first) (move D path second))
      | .inr same => Member.transportChild (same.trans (Equal.ofEq (move_composition D path tail second))).symm
          (pairSecond tail (move D path first) (move D path second)))
    (fun _ tail _ proof =>
      let current := match pairEliminate tail proof with
        | .inl same => Member.transportChild (same.trans (Equal.ofEq (move_composition D path tail first).symm)).symm
            (pairFirst (path ≫ tail) first second)
        | .inr same => Member.transportChild (same.trans (Equal.ofEq (move_composition D path tail second).symm)).symm
            (pairSecond (path ≫ tail) first second)
      Member.transportParent (Equal.ofEq (move_composition D path tail (pair first second))) current)

section Union
variable {point : D} (parent : Value D point)

abbrev UnionOrigin : Type u := Σ target : D, Σ path : point ⟶ target,
  Σ first : Child D (move D path parent), Child D (childValue D (move D path parent) first)

def unionSource (origin : UnionOrigin parent) : D := origin.1
def unionArrival (origin : UnionOrigin parent) : point ⟶ unionSource parent origin := origin.2.1
def unionMiddle (origin : UnionOrigin parent) : Value D (unionSource parent origin) :=
  childValue D (move D (unionArrival parent origin) parent) origin.2.2.1
def unionWitness (origin : UnionOrigin parent) : Value D (unionSource parent origin) :=
  childValue D (unionMiddle parent origin) origin.2.2.2

def union : Value D point :=
  ContextualGraphGenerators.root (unionSource parent) (unionArrival parent) (unionWitness parent) (𝟙 point)

def unionRoot {target : D} (path : point ⟶ target) : Value D target :=
  ContextualGraphGenerators.root (unionSource parent) (unionArrival parent) (unionWitness parent) path

theorem union_move {target : D} (path : point ⟶ target) :
    move D path (union parent) = unionRoot parent path :=
  congrArg (ContextualGraphGenerators.root (unionSource parent) (unionArrival parent) (unionWitness parent))
    (Category.id_comp path)

def unionIntro {target : D} (path : point ⟶ target) {middle value : Value D target}
    (middleMember : Member middle (move D path parent)) (valueMember : Member value middle) :
    Member value (move D path (union parent)) := by
  let inner := Member.transportParent middleMember.2 valueMember
  let origin : UnionOrigin parent := ⟨target, path, middleMember.1, inner.1⟩
  let available := ContextualGraphGenerators.rootIntro (unionSource parent) (unionArrival parent)
    (unionWitness parent) path origin (𝟙 target) (Category.comp_id path)
  let normalized := Member.transportChild
    (Equal.ofEq (move_identity D target (unionWitness parent origin))) available
  exact Member.transportParent (Equal.ofEq (union_move parent path).symm)
    (Member.transportChild inner.2.symm normalized)

def unionEliminate {target : D} (path : point ⟶ target) {value : Value D target}
    (proof : Member value (move D path (union parent))) :
    Σ middle : Value D target, Member middle (move D path parent) × Member value middle := by
  let current := Member.transportParent (Equal.ofEq (union_move parent path)) proof
  let decoded := ContextualGraphGenerators.rootDecode (unionSource parent) (unionArrival parent)
    (unionWitness parent) path current.1
  let origin := decoded.1
  let tail := decoded.2.1
  have same := decoded.2.2.1.down
  have parentSame : move D tail (move D (unionArrival parent origin) parent) = move D path parent :=
    (move_composition D (unionArrival parent origin) tail parent).symm.trans
      (congrArg (fun arrow => move D arrow parent) same)
  let source := Member.restrict tail
    (Member.atChild (move D (unionArrival parent origin) parent) origin.2.2.1)
  let inside := Member.restrict tail
    (Member.atChild (unionMiddle parent origin) origin.2.2.2)
  exact ⟨move D tail (unionMiddle parent origin),
    Member.transportParent (Equal.ofEq parentSame) source,
    Member.transportChild (current.2.trans decoded.2.2.2).symm inside⟩

end Union

def unionCongruence {point : D} {first second : Value D point} (same : Equal first second) :
    Equal (union first) (union second) :=
  extensionality
    (fun _ path _ proof =>
      let decoded := unionEliminate first path proof
      unionIntro second path (Member.transportParent (same.restrict path) decoded.2.1) decoded.2.2)
    (fun _ path _ proof =>
      let decoded := unionEliminate second path proof
      unionIntro first path (Member.transportParent (same.restrict path).symm decoded.2.1) decoded.2.2)

def unionReindex {point target : D} (path : point ⟶ target) (parent : Value D point) :
    Equal (move D path (union parent)) (union (move D path parent)) :=
  extensionality
    (fun _ tail _ proof =>
      let normalized := Member.transportParent (Equal.ofEq (move_composition D path tail (union parent)).symm) proof
      let decoded := unionEliminate parent (path ≫ tail) normalized
      unionIntro (move D path parent) tail
        (Member.transportParent (Equal.ofEq (move_composition D path tail parent)) decoded.2.1) decoded.2.2)
    (fun _ tail _ proof =>
      let decoded := unionEliminate (move D path parent) tail proof
      let current := unionIntro parent (path ≫ tail)
        (Member.transportParent (Equal.ofEq (move_composition D path tail parent).symm) decoded.2.1) decoded.2.2
      Member.transportParent (Equal.ofEq (move_composition D path tail (union parent))) current)

def successor {point : D} (value : Value D point) : Value D point :=
  union (pair value (pair value value))

def successorOld {point target : D} (path : point ⟶ target) {parent : Value D point}
    {value : Value D target} (proof : Member value (move D path parent)) :
    Member value (move D path (successor parent)) :=
  unionIntro _ path (pairFirst path parent (pair parent parent)) proof

def successorSelf {point target : D} (path : point ⟶ target) {parent : Value D point}
    {value : Value D target} (same : Equal value (move D path parent)) :
    Member value (move D path (successor parent)) :=
  unionIntro _ path (pairSecond path parent (pair parent parent))
    (Member.transportChild same.symm (pairFirst path parent parent))

def successorEliminate {point target : D} (path : point ⟶ target) {parent : Value D point}
    {value : Value D target} (proof : Member value (move D path (successor parent))) :
    Member value (move D path parent) ⊕ Equal value (move D path parent) :=
  let decoded := unionEliminate _ path proof
  match pairEliminate path decoded.2.1 with
  | .inl same => .inl (Member.transportParent same decoded.2.2)
  | .inr same => match pairEliminate path (Member.transportParent same decoded.2.2) with
      | .inl same => .inr same
      | .inr same => .inr same

def successorCongruence {point : D} {first second : Value D point} (same : Equal first second) :
    Equal (successor first) (successor second) :=
  extensionality
    (fun _ path _ proof => match successorEliminate path proof with
      | .inl old => successorOld path (Member.transportParent (same.restrict path) old)
      | .inr self => successorSelf path (self.trans (same.restrict path)))
    (fun _ path _ proof => match successorEliminate path proof with
      | .inl old => successorOld path (Member.transportParent (same.restrict path).symm old)
      | .inr self => successorSelf path (self.trans (same.restrict path).symm))

def successorReindex {point target : D} (path : point ⟶ target) (value : Value D point) :
    Equal (move D path (successor value)) (successor (move D path value)) :=
  (unionReindex path (pair value (pair value value))).trans
    (unionCongruence ((pairReindex path value (pair value value)).trans
      (pairCongruence (Equal.refl _) (pairReindex path value value))))

inductive OrdinalEdge : Option (ULift.{u} Nat) → Option (ULift.{u} Nat) → Prop
  | infinite (index : Nat) : OrdinalEdge none (some ⟨index⟩)
  | finite (bound index : Nat) (small : index < bound) : OrdinalEdge (some ⟨bound⟩) (some ⟨index⟩)

def ordinalDiagram (D : Type u) [Category.{u} D] : Diagram D where
  nodes :=
    { obj := fun _ => Option (ULift.{u} Nat)
      map := fun _ => TypeCat.ofHom id
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  edge := fun _ => OrdinalEdge
  edge_transport := fun {_ _} _ {_ _} edge => edge

def ordinal (point : D) (bound : Nat) : Value D point :=
  ⟨ordinalDiagram D, some ⟨bound⟩⟩

def infinity (point : D) : Value D point := ⟨ordinalDiagram D, none⟩

theorem ordinal_move {point target : D} (path : point ⟶ target) (bound : Nat) :
    move D path (ordinal point bound) = ordinal target bound := rfl

theorem infinity_move {point target : D} (path : point ⟶ target) :
    move D path (infinity point) = infinity target := rfl

def ordinalIntro {point : D} {index bound : Nat} {value : Value D point}
    (small : index < bound) (same : Equal value (ordinal point index)) :
    Member value (ordinal point bound) :=
  ⟨⟨some ⟨index⟩, OrdinalEdge.finite bound index small⟩, same⟩

def ordinalEliminate {point : D} (bound : Nat) {value : Value D point}
    (proof : Member value (ordinal point bound)) :
    Σ index : Fin bound, Equal value (ordinal point index.val) := by
  rcases proof with ⟨⟨child, edge⟩, same⟩
  cases child with
  | none => exact False.elim (by cases edge)
  | some index =>
    have small : index.down < bound := by cases edge with | finite _ _ small => exact small
    exact ⟨⟨index.down, small⟩, same⟩

def ordinalZero (point : D) : Equal (ordinal point 0) (empty point) :=
  extensionality
    (fun _ _ _ proof => False.elim (Nat.not_lt_zero _ (ordinalEliminate 0 proof).1.isLt))
    (fun _ path _ proof => PEmpty.elim (emptyEliminate path proof))

def ordinalSuccessor (point : D) (bound : Nat) :
    Equal (ordinal point (bound+1)) (successor (ordinal point bound)) :=
  extensionality
    (fun _ path _ proof =>
      let decoded := ordinalEliminate (bound+1) proof
      if smaller : decoded.1.val < bound then
        successorOld path (ordinalIntro smaller decoded.2)
      else
        let same : decoded.1.val = bound := by omega
        successorSelf path (same ▸ decoded.2))
    (fun _ path _ proof => match successorEliminate path proof with
      | .inl old =>
          let decoded := ordinalEliminate bound old
          ordinalIntro (Nat.lt_trans decoded.1.isLt (Nat.lt_succ_self bound)) decoded.2
      | .inr self => ordinalIntro (Nat.lt_succ_self bound) self)

def infinityIntro {point : D} (index : Nat) {value : Value D point}
    (same : Equal value (ordinal point index)) : Member value (infinity point) :=
  ⟨⟨some ⟨index⟩, OrdinalEdge.infinite index⟩, same⟩

def infinityEliminate {point : D} {value : Value D point} (proof : Member value (infinity point)) :
    Σ index : Nat, Equal value (ordinal point index) := by
  rcases proof with ⟨⟨child, edge⟩, same⟩
  cases child with
  | none => exact False.elim (by cases edge)
  | some index => exact ⟨index.down, same⟩

def infinityEmpty (point : D) : Member (empty point) (infinity point) :=
  infinityIntro 0 (ordinalZero point).symm

def infinitySuccessor {point : D} {value : Value D point} (proof : Member value (infinity point)) :
    Member (successor value) (infinity point) :=
  let decoded := infinityEliminate proof
  infinityIntro (decoded.1+1)
    ((successorCongruence decoded.2).trans (ordinalSuccessor point decoded.1).symm)

theorem ordinal_irreflexive (point : D) (bound : Nat) :
    Member (ordinal point bound) (ordinal point bound) → False := by
  induction bound using Nat.strong_induction_on with
  | h bound previous =>
    intro proof
    let decoded := ordinalEliminate bound proof
    let smaller := ordinalIntro decoded.1.isLt (Equal.refl (ordinal point decoded.1.val))
    exact previous decoded.1.val decoded.1.isLt (Member.transportParent decoded.2 smaller)

theorem ordinal_matching_bounds {point : D} {first second : Nat}
    (proof : Equal (ordinal point first) (ordinal point second)) : first = second := by
  rcases Nat.lt_trichotomy first second with smaller | same | larger
  · exact False.elim (ordinal_irreflexive point first
      (Member.transportParent proof.symm (ordinalIntro smaller (Equal.refl _))))
  · exact same
  · exact False.elim (ordinal_irreflexive point second
      (Member.transportParent proof (ordinalIntro larger (Equal.refl _))))

theorem ordinal_matching_iff (point : D) (first second : Nat) :
    Nonempty (Equal (ordinal point first) (ordinal point second)) ↔ first = second := by
  constructor
  · rintro ⟨proof⟩
    exact ordinal_matching_bounds proof
  · intro same
    subst second
    exact ⟨Equal.refl _⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetConstructors
