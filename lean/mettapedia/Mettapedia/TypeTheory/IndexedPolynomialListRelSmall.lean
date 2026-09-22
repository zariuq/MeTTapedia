import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Small, witness-retaining fibres of the polynomial List relator

For fixed endpoint lists, pointwise relational evidence lives in the universe
of the element relation, independently of the universes of the endpoints.
The recursive spine below retains every head witness. Its explicit inverse
maps identify it with the existing `ListExample.ListRel`, whose inductive
presentation lives in the maximum of the three universes.

The same equivalence applies to the existing polynomial `mapRel`. Evidence
maps and endpoint reindexing commute with the constructor interpretation.
This supplies a small semantic fibre for a declaration whose result universe
is the relation universe; it neither imposes an order on the element and
relation levels nor interprets an entire native calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.ListExample.ListRelSmall

universe u v w u' v' w' w''

variable {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}

/-- At fixed endpoints, only relation witnesses contribute to the fibre
universe. Mismatched list shapes have no witness. -/
def Spine (relation : A → B → Type w) : List A → List B → Type w
  | [], [] => PUnit
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty
  | left :: lefts, right :: rights =>
      relation left right × Spine relation lefts rights

variable {relation : A → B → Type w}

/-- Reconstruct the existing inductive relator, retaining every witness. -/
def toListRel : {lefts : List A} → {rights : List B} →
    Spine relation lefts rights → ListRel relation lefts rights
  | [], [], _ => .nil
  | [], _ :: _, impossible => nomatch impossible
  | _ :: _, [], impossible => nomatch impossible
  | _ :: _, _ :: _, ⟨head, tail⟩ => .cons head (toListRel tail)

/-- Read the existing inductive evidence into its smaller fixed-index fibre. -/
def ofListRel : {lefts : List A} → {rights : List B} →
    ListRel relation lefts rights → Spine relation lefts rights
  | _, _, .nil => PUnit.unit
  | _, _, .cons head tail => ⟨head, ofListRel tail⟩

@[simp] theorem toListRel_nil :
    toListRel (relation := relation) (lefts := []) (rights := []) PUnit.unit =
      ListRel.nil := rfl

@[simp] theorem toListRel_cons {left : A} {right : B}
    {lefts : List A} {rights : List B} (head : relation left right)
    (tail : Spine relation lefts rights) :
    toListRel (lefts := left :: lefts) (rights := right :: rights) ⟨head, tail⟩ =
      ListRel.cons head (toListRel tail) := rfl

@[simp] theorem ofListRel_nil :
    ofListRel (ListRel.nil : ListRel relation [] []) = PUnit.unit := rfl

@[simp] theorem ofListRel_cons {left : A} {right : B}
    {lefts : List A} {rights : List B} (head : relation left right)
    (tail : ListRel relation lefts rights) :
    ofListRel (ListRel.cons head tail) = (head, ofListRel tail) := rfl

@[simp] theorem ofListRel_toListRel {lefts : List A} {rights : List B}
    (evidence : Spine relation lefts rights) :
    ofListRel (toListRel evidence) = evidence := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => cases evidence; rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [toListRel, ofListRel, inductionHypothesis tail]
          rfl

@[simp] theorem toListRel_ofListRel {lefts : List A} {rights : List B}
    (evidence : ListRel relation lefts rights) :
    toListRel (ofListRel evidence) = evidence := by
  induction evidence with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [ofListRel, toListRel, inductionHypothesis]

/-- Full equivalence of evidence types, not merely of their supports. -/
def equivListRel (relation : A → B → Type w) (lefts : List A) (rights : List B) :
    Spine relation lefts rights ≃ ListRel relation lefts rights where
  toFun := toListRel
  invFun := ofListRel
  left_inv := ofListRel_toListRel
  right_inv := toListRel_ofListRel

theorem toListRel_injective (lefts : List A) (rights : List B) :
    Function.Injective (toListRel (relation := relation) (lefts := lefts) (rights := rights)) :=
  (equivListRel relation lefts rights).injective

/-! ## Pointwise maps of retained evidence -/

/-- Transform every head witness without changing endpoint lists or shape. -/
def mapEvidence {later : A → B → Type w'}
    (mapping : ∀ left right, relation left right → later left right) :
    {lefts : List A} → {rights : List B} →
      Spine relation lefts rights → Spine later lefts rights
  | [], [], _ => PUnit.unit
  | [], _ :: _, impossible => nomatch impossible
  | _ :: _, [], impossible => nomatch impossible
  | _ :: _, _ :: _, ⟨head, tail⟩ =>
      ⟨mapping _ _ head, mapEvidence mapping tail⟩

@[simp] theorem mapEvidence_nil {later : A → B → Type w'}
    (mapping : ∀ left right, relation left right → later left right) :
    mapEvidence mapping (lefts := []) (rights := []) PUnit.unit = PUnit.unit := rfl

@[simp] theorem mapEvidence_cons {later : A → B → Type w'}
    (mapping : ∀ left right, relation left right → later left right)
    {left : A} {right : B} {lefts : List A} {rights : List B}
    (head : relation left right) (tail : Spine relation lefts rights) :
    mapEvidence mapping (lefts := left :: lefts) (rights := right :: rights) ⟨head, tail⟩ =
      (mapping left right head, mapEvidence mapping tail) := rfl

@[simp] theorem mapEvidence_id {lefts : List A} {rights : List B}
    (evidence : Spine relation lefts rights) :
    mapEvidence (fun _ _ value => value) evidence = evidence := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => cases evidence; rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [mapEvidence, inductionHypothesis tail]
          rfl

theorem mapEvidence_comp {middle : A → B → Type w'} {later : A → B → Type w''}
    (first : ∀ left right, relation left right → middle left right)
    (second : ∀ left right, middle left right → later left right)
    {lefts : List A} {rights : List B} (evidence : Spine relation lefts rights) :
    mapEvidence second (mapEvidence first evidence) =
      mapEvidence (fun left right value => second left right (first left right value)) evidence := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [mapEvidence, inductionHypothesis tail]
          rfl

/-- The existing same-universe evidence action is exactly reconstructed. -/
theorem toListRel_mapEvidence {later : A → B → Type w}
    (mapping : ∀ left right, relation left right → later left right)
    {lefts : List A} {rights : List B} (evidence : Spine relation lefts rights) :
    toListRel (mapEvidence mapping evidence) =
      ListRel.mapEvidence mapping (toListRel evidence) := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [mapEvidence, toListRel, ListRel.mapEvidence, inductionHypothesis tail]

/-! ## Endpoint reindexing, including noninjective maps -/

/-- Reindex an element relation and map the actual endpoint lists. The
evidence values are untouched; no injectivity of either map is assumed. -/
def reindex (leftMap : C → A) (rightMap : D → B) :
    {lefts : List C} → {rights : List D} →
      Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights →
        Spine relation (lefts.map leftMap) (rights.map rightMap)
  | [], [], _ => PUnit.unit
  | [], _ :: _, impossible => nomatch impossible
  | _ :: _, [], impossible => nomatch impossible
  | _ :: _, _ :: _, ⟨head, tail⟩ => ⟨head, reindex leftMap rightMap tail⟩

/-- Recover a reindexed spine at its retained original endpoint lists. -/
def unreindex (leftMap : C → A) (rightMap : D → B) :
    {lefts : List C} → {rights : List D} →
      Spine relation (lefts.map leftMap) (rights.map rightMap) →
        Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights
  | [], [], _ => PUnit.unit
  | [], _ :: _, impossible => nomatch impossible
  | _ :: _, [], impossible => nomatch impossible
  | _ :: _, _ :: _, ⟨head, tail⟩ => ⟨head, unreindex leftMap rightMap tail⟩

@[simp] theorem unreindex_reindex (leftMap : C → A) (rightMap : D → B)
    {lefts : List C} {rights : List D}
    (evidence : Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights) :
    unreindex leftMap rightMap (reindex leftMap rightMap evidence) = evidence := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => cases evidence; rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [reindex, unreindex, inductionHypothesis tail]
          rfl

@[simp] theorem reindex_unreindex (leftMap : C → A) (rightMap : D → B)
    {lefts : List C} {rights : List D}
    (evidence : Spine relation (lefts.map leftMap) (rights.map rightMap)) :
    reindex leftMap rightMap (unreindex leftMap rightMap evidence) = evidence := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => cases evidence; rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [reindex, unreindex, inductionHypothesis tail]
          rfl

/-- Reindexing is a fibre equivalence at the retained endpoints, even when
the maps identify distinct elements. It is not a recovery of forgotten lists. -/
def reindexEquiv (relation : A → B → Type w) (leftMap : C → A) (rightMap : D → B)
    (lefts : List C) (rights : List D) :
    Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights ≃
      Spine relation (lefts.map leftMap) (rights.map rightMap) where
  toFun := reindex leftMap rightMap
  invFun := unreindex leftMap rightMap
  left_inv := unreindex_reindex leftMap rightMap
  right_inv := reindex_unreindex leftMap rightMap

/-- The endpoint action on existing inductive evidence, defined directly by
its constructors rather than through the new small equivalence. -/
def reindexListRel (leftMap : C → A) (rightMap : D → B) :
    {lefts : List C} → {rights : List D} →
      ListRel (fun left right => relation (leftMap left) (rightMap right)) lefts rights →
        ListRel relation (lefts.map leftMap) (rights.map rightMap)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (reindexListRel leftMap rightMap tail)

/-- Reconstructing and reindexing commute on every retained head witness. -/
theorem toListRel_reindex (leftMap : C → A) (rightMap : D → B)
    {lefts : List C} {rights : List D}
    (evidence : Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights) :
    toListRel (reindex leftMap rightMap evidence) =
      reindexListRel leftMap rightMap (toListRel evidence) := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [reindex, toListRel, reindexListRel, inductionHypothesis tail]

/-- Evidence transport is natural with respect to endpoint reindexing. -/
theorem reindex_mapEvidence {later : A → B → Type w'}
    (mapping : ∀ left right, relation left right → later left right)
    (leftMap : C → A) (rightMap : D → B)
    {lefts : List C} {rights : List D}
    (evidence : Spine (fun left right => relation (leftMap left) (rightMap right)) lefts rights) :
    reindex leftMap rightMap
        (mapEvidence (fun left right => mapping (leftMap left) (rightMap right)) evidence) =
      mapEvidence mapping (reindex leftMap rightMap evidence) := by
  induction lefts generalizing rights with
  | nil =>
      cases rights with
      | nil => rfl
      | cons _ _ => exact nomatch evidence
  | cons left lefts inductionHypothesis =>
      cases rights with
      | nil => exact nomatch evidence
      | cons right rights =>
          rcases evidence with ⟨head, tail⟩
          simp only [reindex, mapEvidence, inductionHypothesis tail]
          rfl

/-! ## The existing polynomial relator -/

/-- The smaller fibre of the existing polynomial List endpoints. -/
noncomputable def mapRelFibre (relation : A → B → Type w)
    (source : ListP A) (target : ListP B) : Type w :=
  Spine relation (toList source) (toList target)

/-- No endpoint universe is added to the small side of this equivalence. -/
noncomputable def mapRelEquiv (relation : A → B → Type w)
    (source : ListP A) (target : ListP B) :
    mapRelFibre relation source target ≃ mapRel relation source target :=
  equivListRel relation (toList source) (toList target)

/-! ## Witness and shape controls -/

def smallBranchLeft : Spine branchingRelation [()] [()] := ⟨.left, PUnit.unit⟩
def smallBranchRight : Spine branchingRelation [()] [()] := ⟨.right, PUnit.unit⟩

theorem branches_distinct : smallBranchLeft ≠ smallBranchRight := by
  intro equal
  have heads := congrArg Prod.fst equal
  exact BranchEvidence.noConfusion heads

theorem reconstructed_branches_distinct :
    toListRel smallBranchLeft ≠ toListRel smallBranchRight :=
  fun equal => branches_distinct ((toListRel_injective [()] [()]) equal)

theorem nil_cons_empty (right : B) (rights : List B) :
    IsEmpty (Spine relation [] (right :: rights)) where
  false evidence := nomatch evidence

theorem cons_nil_empty (left : A) (lefts : List A) :
    IsEmpty (Spine relation (left :: lefts) []) where
  false evidence := nomatch evidence

theorem impossible_singleton_empty : IsEmpty (Spine impossibleRelation [()] [()]) where
  false evidence := evidence.1.elim

/-- Noninjective endpoint substitution preserves both head witnesses. -/
theorem noninjective_reindex_retains_branches :
    reindex (fun _ : Bool => ()) (fun _ : Bool => ())
        (relation := branchingRelation) (lefts := [false]) (rights := [true])
        ⟨BranchEvidence.left, PUnit.unit⟩ ≠
      reindex (fun _ : Bool => ()) (fun _ : Bool => ())
        (relation := branchingRelation) (lefts := [false]) (rights := [true])
        ⟨BranchEvidence.right, PUnit.unit⟩ := by
  intro equal
  exact BranchEvidence.noConfusion (congrArg Prod.fst equal)

#print axioms equivListRel
#print axioms mapEvidence_comp
#print axioms toListRel_mapEvidence
#print axioms reindexEquiv
#print axioms toListRel_reindex
#print axioms reindex_mapEvidence
#print axioms mapRelEquiv
#print axioms reconstructed_branches_distinct
#print axioms noninjective_reindex_retains_branches

end Mettapedia.TypeTheory.IndexedPolynomial.ListExample.ListRelSmall
