import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mathlib.Logic.Equiv.Basic

/-!
# Dependent families over the well-founded inclusion

The inclusion of the well-founded hypersets into all hypersets induces an
equivalence of member fibres: every member of a well-founded hyperset is itself
well-founded.  It consequently preserves dependent sums and sections, including
application and substitution of member indices.  The equivalence with `ZFSet`
also induces an equivalence of member fibres and of their dependent sections.

These comparisons concern the proposition-valued membership of the hyperset
quotient.  They do not erase graph edges or provenance.  No presentation or
choice of a graph is used.  The ambient carriers and their member fibres are in
`Type (u + 1)`; families may take values in any `Sort v`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u v

namespace WellFoundedPart

/-- The well-founded inclusion is an equivalence on the members of a
well-founded hyperset, because well-foundedness is inherited by membership. -/
def memberEquiv (X : WellFoundedPart.{u}) :
    El Mem X ≃ El (fun x X : HSet.{u} => x ∈ X) X.1 where
  toFun a := ⟨a.1.1, a.2⟩
  invFun a := ⟨⟨a.1, X.2.mem a.2⟩, a.2⟩
  left_inv _ := El.ext propositional (Subtype.ext rfl)
  right_inv _ := El.ext HSet.propositional rfl

@[simp] theorem memberEquiv_value (X : WellFoundedPart.{u}) (a : El Mem X) :
    (memberEquiv X a).1 = a.1.1 := rfl

@[simp] theorem memberEquiv_symm_value (X : WellFoundedPart.{u})
    (a : El (fun x X : HSet.{u} => x ∈ X) X.1) :
    ((memberEquiv X).symm a).1.1 = a.1 := rfl

/-- Restricting a dependent sum to the well-founded carrier keeps its index
and its complete dependent value. -/
def memberSigmaEquiv (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v) :
    (Σ' a : El Mem X, P (memberEquiv X a)) ≃
      Σ' a : El (fun x X : HSet.{u} => x ∈ X) X.1, P a where
  toFun a := ⟨memberEquiv X a.1, a.2⟩
  invFun a := ⟨(memberEquiv X).symm a.1, a.2⟩
  left_inv a := by
    rcases a with ⟨⟨⟨x, hx⟩, hmem⟩, value⟩
    rfl
  right_inv a := by
    rcases a with ⟨⟨x, hmem⟩, value⟩
    rfl

@[simp] theorem memberSigmaEquiv_index (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v)
    (a : Σ' a : El Mem X, P (memberEquiv X a)) :
    ((memberSigmaEquiv X P).toFun a).1 = memberEquiv X a.1 := rfl

@[simp] theorem memberSigmaEquiv_value (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v)
    (a : Σ' a : El Mem X, P (memberEquiv X a)) :
    ((memberSigmaEquiv X P).toFun a).2 = a.2 := rfl

/-- Sections over the well-founded member fibre correspond to sections over
the ambient member fibre. -/
def memberPiEquiv (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v) :
    ((a : El Mem X) → P (memberEquiv X a)) ≃
      ((a : El (fun x X : HSet.{u} => x ∈ X) X.1) → P a) where
  toFun s a := s ((memberEquiv X).symm a)
  invFun s a := s (memberEquiv X a)
  left_inv s := by
    funext a
    rcases a with ⟨⟨x, hx⟩, hmem⟩
    rfl
  right_inv s := by
    funext a
    rcases a with ⟨x, hmem⟩
    rfl

/-- Transporting a section preserves its actual result at a transported
argument, not only the existence of a result. -/
@[simp] theorem memberPiEquiv_apply (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v)
    (s : (a : El Mem X) → P (memberEquiv X a)) (a : El Mem X) :
    (memberPiEquiv X P).toFun s (memberEquiv X a) = s a := by
  rcases a with ⟨⟨x, hx⟩, hmem⟩
  rfl

@[simp] theorem memberPiEquiv_symm_apply (X : WellFoundedPart.{u})
    (P : El (fun x X : HSet.{u} => x ∈ X) X.1 → Sort v)
    (s : (a : El (fun x X : HSet.{u} => x ∈ X) X.1) → P a) (a : El Mem X) :
    (memberPiEquiv X P).symm.toFun s a = s (memberEquiv X a) := rfl

/-- A substitution of member indices viewed in the ambient hyperset carrier. -/
def ambientMemberMap {X Y : WellFoundedPart.{u}} (f : El Mem X → El Mem Y) :
    El (fun x X : HSet.{u} => x ∈ X) X.1 → El (fun x X : HSet.{u} => x ∈ X) Y.1 :=
  fun a => memberEquiv Y (f ((memberEquiv X).symm a))

@[simp] theorem ambientMemberMap_apply {X Y : WellFoundedPart.{u}}
    (f : El Mem X → El Mem Y) (a : El Mem X) :
    ambientMemberMap f (memberEquiv X a) = memberEquiv Y (f a) := by
  exact congrArg (fun b => memberEquiv Y (f b)) ((memberEquiv X).symm_apply_apply a)

/-- Reindexing a dependent section and passing to the ambient carrier commute. -/
theorem memberPiEquiv_substitution {X Y : WellFoundedPart.{u}}
    (f : El Mem X → El Mem Y)
    (P : El (fun x X : HSet.{u} => x ∈ X) Y.1 → Sort v)
    (s : (a : El Mem Y) → P (memberEquiv Y a)) :
    (memberPiEquiv X (fun a => P (ambientMemberMap f a))).toFun (fun a => s (f a)) =
      fun a => (memberPiEquiv Y P).toFun s (ambientMemberMap f a) := by
  funext a
  rcases a with ⟨x, hmem⟩
  rfl

/-- Equality transport of sets is compatible with the well-founded inclusion. -/
theorem memberEquiv_transport {X Y : WellFoundedPart.{u}} (h : X = Y) (a : El Mem X) :
    memberEquiv Y (transport (Mem := Mem) h a) =
      transport (Mem := fun x X : HSet.{u} => x ∈ X)
        (congrArg Subtype.val h) (memberEquiv X a) := by
  cases h
  rfl

/-! ## Material dependent pairs -/

/-- A well-founded-set-valued family viewed over the ambient member fibre. -/
def ambientFamily (X : WellFoundedPart.{u}) (B : El Mem X → WellFoundedPart.{u})
    (a : El (fun x X : HSet.{u} => x ∈ X) X.1) : HSet.{u} :=
  (B ((memberEquiv X).symm a)).1

/-- Dependent pairs of actual set members transport across the well-founded
inclusion on both the base and the dependent fibre. -/
def dependentMemberSigmaEquiv (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    (Σ' a : El Mem X, El Mem (B a)) ≃
      Σ' a : El (fun x X : HSet.{u} => x ∈ X) X.1,
        El (fun x X : HSet.{u} => x ∈ X) (ambientFamily X B a) where
  toFun a := ⟨memberEquiv X a.1, memberEquiv (B a.1) a.2⟩
  invFun a := ⟨(memberEquiv X).symm a.1,
    (memberEquiv (B ((memberEquiv X).symm a.1))).symm a.2⟩
  left_inv a := by
    rcases a with ⟨⟨⟨x, hx⟩, hmem⟩, ⟨⟨y, hy⟩, hmem'⟩⟩
    rfl
  right_inv a := by
    rcases a with ⟨⟨x, hmem⟩, ⟨y, hmem'⟩⟩
    rfl

/-- A section which returns a member of each well-founded fibre is equivalent
to an ambient section returning a member of the corresponding hyperset. -/
def dependentMemberPiEquiv (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    ((a : El Mem X) → El Mem (B a)) ≃
      ((a : El (fun x X : HSet.{u} => x ∈ X) X.1) →
        El (fun x X : HSet.{u} => x ∈ X) (ambientFamily X B a)) where
  toFun s a := memberEquiv (B ((memberEquiv X).symm a)) (s ((memberEquiv X).symm a))
  invFun s a := (memberEquiv (B a)).symm (s (memberEquiv X a))
  left_inv s := by
    funext a
    rcases a with ⟨⟨x, hx⟩, hmem⟩
    exact (memberEquiv (B ⟨⟨x, hx⟩, hmem⟩)).symm_apply_apply _
  right_inv s := by
    funext a
    rcases a with ⟨x, hmem⟩
    exact (memberEquiv (B ((memberEquiv X).symm ⟨x, hmem⟩))).apply_symm_apply _

/-- Application commutes with the member comparison on the dependent fibre. -/
theorem dependentMemberPiEquiv_apply (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (s : (a : El Mem X) → El Mem (B a))
    (a : El Mem X) :
    dependentMemberPiEquiv X B s (memberEquiv X a) = memberEquiv (B a) (s a) := by
  rcases a with ⟨⟨x, hx⟩, hmem⟩
  rfl

/-- In particular, application retains the actual returned hyperset value. -/
theorem dependentMemberPiEquiv_apply_value (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (s : (a : El Mem X) → El Mem (B a))
    (a : El Mem X) :
    (dependentMemberPiEquiv X B s (memberEquiv X a)).1 = (s a).1.1 :=
  congrArg PSigma.fst (dependentMemberPiEquiv_apply X B s a)

/-- Reindexing a material member-valued section commutes with the inclusion
on both its argument and its returned dependent value. -/
theorem dependentMemberPiEquiv_substitution {X Y : WellFoundedPart.{u}}
    (f : El Mem X → El Mem Y) (B : El Mem Y → WellFoundedPart.{u})
    (s : (a : El Mem Y) → El Mem (B a)) :
    dependentMemberPiEquiv X (fun a => B (f a)) (fun a => s (f a)) =
      fun a => dependentMemberPiEquiv Y B s (ambientMemberMap f a) := by
  funext a
  rcases a with ⟨x, hmem⟩
  rfl

/-- The dependent-pair transport retains the represented ordered pair. -/
theorem dependentMemberSigmaEquiv_pairValue (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (a : Σ' a : El Mem X, El Mem (B a)) :
    HSet.kpair ((dependentMemberSigmaEquiv X B) a).1.1
        ((dependentMemberSigmaEquiv X B) a).2.1 = HSet.kpair a.1.1.1 a.2.1.1 := rfl

/-- The two material encodings of a dependent sum are compared by their
proved decoding equivalences, with the well-founded inclusion on both fibres. -/
def sigmaSetMemberEquiv (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    El Mem (sigmaSet (dependentReplacement p) union pairing X B) ≃
      El (fun x X : HSet.{u} => x ∈ X)
        (sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski X.1
          (ambientFamily X B)) :=
  (sigmaSetEquiv p X B).trans ((dependentMemberSigmaEquiv X B).trans
    (HSet.sigmaSetEquiv p X.1 (ambientFamily X B)).symm)

/-- The material sum comparison keeps the actual hyperset value. -/
theorem sigmaSetMemberEquiv_value (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u})
    (a : El Mem (sigmaSet (dependentReplacement p) union pairing X B)) :
    (sigmaSetMemberEquiv p X B a).1 = a.1.1 := by
  obtain ⟨ab, rfl⟩ := (sigmaSetEquiv p X B).symm.surjective a
  simp only [sigmaSetMemberEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact dependentMemberSigmaEquiv_pairValue X B ab

/-- The material set of dependent pairs itself is preserved by inclusion. -/
theorem sigmaSet_value (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    (sigmaSet (dependentReplacement p) union pairing X B).1 =
      sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski X.1
        (ambientFamily X B) := by
  apply HSet.ext
  intro z
  constructor
  · intro hz
    let a : El Mem (sigmaSet (dependentReplacement p) union pairing X B) :=
      ⟨⟨z, (sigmaSet (dependentReplacement p) union pairing X B).2.mem hz⟩, hz⟩
    have preserved : (sigmaSetMemberEquiv p X B a).1 = z :=
      sigmaSetMemberEquiv_value p X B a
    rw [← preserved]
    exact (sigmaSetMemberEquiv p X B a).2
  · intro hz
    obtain ⟨a, ha⟩ := (sigmaSetMemberEquiv p X B).surjective ⟨z, hz⟩
    have preserved := sigmaSetMemberEquiv_value p X B a
    have value : a.1.1 = z := preserved.symm.trans (congrArg PSigma.fst ha)
    rw [← value]
    exact a.2

/-! ## Material dependent functions -/

/-- A function's material graph has the same hyperset value after including
both the argument and the returned member into the ambient carrier. -/
theorem functionGraph_value (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (s : (a : El Mem X) → El Mem (B a)) :
    (functionGraph (dependentReplacement p) pairing s).1 =
      functionGraph (HSet.dependentReplacement p) HSet.kuratowski
        (dependentMemberPiEquiv X B s) := by
  apply HSet.ext
  intro z
  constructor
  · intro hz
    let zWF : WellFoundedPart.{u} :=
      ⟨z, (functionGraph (dependentReplacement p) pairing s).2.mem hz⟩
    have hzWF : Mem zWF (functionGraph (dependentReplacement p) pairing s) := hz
    obtain ⟨a, ha⟩ := (dependentReplacement p).exists_of_mem_image hzWF
    change z ∈ HSet.image p X.1 fun a => HSet.kpair a.1 (dependentMemberPiEquiv X B s a).1
    apply HSet.mem_image.mpr
    refine ⟨memberEquiv X a, ?_⟩
    change HSet.kpair a.1.1 (dependentMemberPiEquiv X B s (memberEquiv X a)).1 = z
    rw [dependentMemberPiEquiv_apply_value]
    exact congrArg Subtype.val ha
  · intro hz
    change z ∈ HSet.image p X.1 (fun a => HSet.kpair a.1
      (dependentMemberPiEquiv X B s a).1) at hz
    obtain ⟨a, ha⟩ := HSet.mem_image.mp hz
    have included := (dependentReplacement p).mem_image
      (fun b => pairing.pair b.1 (s b).1) ((memberEquiv X).symm a)
    have value : (pairing.pair ((memberEquiv X).symm a).1
        (s ((memberEquiv X).symm a)).1).1 = z := ha
    exact value ▸ included

/-- The actual material dependent products are compared through their proved
decoding into dependent functions and the value-retaining family comparison. -/
def piSetMemberEquiv (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    El Mem (dependentProduct p X B) ≃
      El (fun x X : HSet.{u} => x ∈ X)
        (HSet.dependentProduct p X.1 (ambientFamily X B)) :=
  (piSetEquiv p X B).trans ((dependentMemberPiEquiv X B).trans
    (HSet.piSetEquiv p X.1 (ambientFamily X B)).symm)

/-- Product-member transport retains the entire extensional function graph. -/
theorem piSetMemberEquiv_value (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (g : El Mem (dependentProduct p X B)) :
    (piSetMemberEquiv p X B g).1 = g.1.1 := by
  obtain ⟨s, rfl⟩ := (piSetEquiv p X B).symm.surjective g
  simp only [piSetMemberEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (functionGraph_value p X B s).symm

/-- The material dependent-product set itself is preserved by inclusion. -/
theorem dependentProduct_value (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    (dependentProduct p X B).1 = HSet.dependentProduct p X.1 (ambientFamily X B) := by
  apply HSet.ext
  intro G
  constructor
  · intro hG
    let g : El Mem (dependentProduct p X B) := ⟨⟨G, (dependentProduct p X B).2.mem hG⟩, hG⟩
    have preserved : (piSetMemberEquiv p X B g).1 = G := piSetMemberEquiv_value p X B g
    rw [← preserved]
    exact (piSetMemberEquiv p X B g).2
  · intro hG
    obtain ⟨g, hg⟩ := (piSetMemberEquiv p X B).surjective ⟨G, hG⟩
    have value : g.1.1 = G :=
      (piSetMemberEquiv_value p X B g).symm.trans (congrArg PSigma.fst hg)
    rw [← value]
    exact g.2

/-- Evaluating either material product gives the same member of the dependent
fibre, with the well-founded inclusion applied to that returned member. -/
theorem piSetMemberEquiv_evaluation (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) (g : El Mem (dependentProduct p X B))
    (a : El Mem X) :
    HSet.piSetEquiv p X.1 (ambientFamily X B) (piSetMemberEquiv p X B g) (memberEquiv X a) =
      memberEquiv (B a) (piSetEquiv p X B g a) := by
  simp only [piSetMemberEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact dependentMemberPiEquiv_apply X B (piSetEquiv p X B g) a

/-- The `ZFSet` comparison is an equivalence on actual member fibres. -/
def zfMemberEquiv (X : WellFoundedPart.{u}) :
    El Mem X ≃ El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) where
  toFun a := ⟨HSet.wellFoundedPartEquivZFSet a.1,
    HSet.wellFoundedPartEquivZFSet_mem_iff.mpr a.2⟩
  invFun a := ⟨HSet.wellFoundedPartEquivZFSet.symm a.1, mem_symm_of_mem a.2⟩
  left_inv a := El.ext propositional (HSet.wellFoundedPartEquivZFSet.symm_apply_apply a.1)
  right_inv a := El.ext Instances.ZFSetModel.propositional
    (HSet.wellFoundedPartEquivZFSet.apply_symm_apply a.1)

/-- The `ZFSet` member comparison preserves the represented ambient hyperset. -/
theorem zfMemberEquiv_value (X : WellFoundedPart.{u}) (a : El Mem X) :
    HSet.ofZFSet (zfMemberEquiv X a).1 = (memberEquiv X a).1 :=
  ofZFSet_equiv a.1

@[simp] theorem zfMemberEquiv_symm_value (X : WellFoundedPart.{u})
    (a : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X)) :
    ((zfMemberEquiv X).symm a).1.1 = HSet.ofZFSet a.1 := rfl

/-- Set equality transport also commutes with the `ZFSet` member comparison. -/
theorem zfMemberEquiv_transport {X Y : WellFoundedPart.{u}} (h : X = Y) (a : El Mem X) :
    zfMemberEquiv Y (transport (Mem := Mem) h a) =
      transport (Mem := Instances.ZFSetModel.Mem)
        (congrArg HSet.wellFoundedPartEquivZFSet h) (zfMemberEquiv X a) := by
  cases h
  rfl

/-- Dependent sums over `ZFSet` transport through the member comparison. -/
def zfMemberSigmaEquiv (X : WellFoundedPart.{u})
    (P : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) → Type v) :
    (Σ' a : El Mem X, P (zfMemberEquiv X a)) ≃
      Σ' a : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X), P a :=
  (Equiv.psigmaEquivSigma fun a => P (zfMemberEquiv X a)).trans
    ((Equiv.sigmaCongrLeft (zfMemberEquiv X)).trans (Equiv.psigmaEquivSigma P).symm)

@[simp] theorem zfMemberSigmaEquiv_index (X : WellFoundedPart.{u})
    (P : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) → Type v)
    (a : Σ' a : El Mem X, P (zfMemberEquiv X a)) :
    (zfMemberSigmaEquiv X P a).1 = zfMemberEquiv X a.1 := rfl

@[simp] theorem zfMemberSigmaEquiv_value (X : WellFoundedPart.{u})
    (P : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) → Type v)
    (a : Σ' a : El Mem X, P (zfMemberEquiv X a)) :
    (zfMemberSigmaEquiv X P a).2 = a.2 := rfl

/-- Dependent sections, including nonconstant families, transport to `ZFSet`. -/
def zfMemberPiEquiv (X : WellFoundedPart.{u})
    (P : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) → Sort v) :
    ((a : El Mem X) → P (zfMemberEquiv X a)) ≃
      ((a : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X)) → P a) where
  toFun s a := cast (congrArg P ((zfMemberEquiv X).apply_symm_apply a))
    (s ((zfMemberEquiv X).symm a))
  invFun s a := s (zfMemberEquiv X a)
  left_inv s := by
    funext a
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq s ((zfMemberEquiv X).symm_apply_apply a)))
  right_inv s := by
    funext a
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq s ((zfMemberEquiv X).apply_symm_apply a)))

@[simp] theorem zfMemberPiEquiv_apply (X : WellFoundedPart.{u})
    (P : El Instances.ZFSetModel.Mem (HSet.wellFoundedPartEquivZFSet X) → Sort v)
    (s : (a : El Mem X) → P (zfMemberEquiv X a)) (a : El Mem X) :
    (zfMemberPiEquiv X P).toFun s (zfMemberEquiv X a) = s a := by
  exact eq_of_heq ((cast_heq _ _).trans
    (congr_arg_heq s ((zfMemberEquiv X).symm_apply_apply a)))

/-- The ambient member equivalence cannot be extended by adding a
well-founded representative of the quine atom. -/
theorem no_wellFounded_representative_quineAtom :
    ¬ ∃ X : WellFoundedPart.{u}, X.1 = HSet.quineAtom := by
  rintro ⟨X, h⟩
  exact ne_quineAtom X h

/-! ## A genuinely varying member family -/

/-- A well-founded base with the distinct members `∅` and `{∅}`. -/
def emptySingletonBase : WellFoundedPart.{u} :=
  ⟨{∅, {∅}}, HSet.wf_empty.pair HSet.wf_singleton_empty⟩

def emptyIndex : El Mem emptySingletonBase.{u} :=
  ⟨empty, HSet.mem_pair.mpr (Or.inl rfl)⟩

def singletonIndex : El Mem emptySingletonBase.{u} :=
  ⟨⟨{∅}, HSet.wf_singleton_empty⟩, HSet.mem_pair.mpr (Or.inr rfl)⟩

/-- Each member determines its own singleton fibre in the well-founded part. -/
def singletonMemberFamily {X : WellFoundedPart.{u}} (a : El Mem X) : WellFoundedPart.{u} :=
  ⟨{a.1.1}, a.1.2.singleton⟩

/-- A genuine dependent section returns its input as a member of that input's
singleton, carrying the membership needed for the dependent result. -/
def singletonMemberSection (X : WellFoundedPart.{u}) (a : El Mem X) :
    El Mem (singletonMemberFamily a) :=
  ⟨a.1, HSet.mem_singleton_self a.1.1⟩

/-- Application of the transported singleton section retains its input
hyperset. -/
theorem singletonMemberSection_application (X : WellFoundedPart.{u}) (a : El Mem X) :
    (dependentMemberPiEquiv X singletonMemberFamily (singletonMemberSection X)
      (memberEquiv X a)).1 = a.1.1 :=
  dependentMemberPiEquiv_apply_value X singletonMemberFamily (singletonMemberSection X) a

/-- The actual dependent section distinguishes the two members of the
example base, including after its ambient transport. -/
theorem singletonMemberSection_results_distinct :
    (dependentMemberPiEquiv emptySingletonBase.{u} singletonMemberFamily
      (singletonMemberSection emptySingletonBase) (memberEquiv emptySingletonBase emptyIndex)).1 ≠
    (dependentMemberPiEquiv emptySingletonBase singletonMemberFamily
      (singletonMemberSection emptySingletonBase)
      (memberEquiv emptySingletonBase singletonIndex)).1 := by
  rw [singletonMemberSection_application, singletonMemberSection_application]
  exact HSet.empty_ne_singleton_empty

/-- The fibre is the type of members of the selected set, so it varies with
the base member rather than being a constant simple-type family. -/
def memberOfMemberFamily
    (a : El (fun x X : HSet.{u} => x ∈ X) emptySingletonBase.1) : Type (u + 1) :=
  El (fun x X : HSet.{u} => x ∈ X) a.1

/-- The fibre at `∅` is empty. -/
instance : IsEmpty (memberOfMemberFamily.{u} (memberEquiv emptySingletonBase emptyIndex)) :=
  ⟨fun a => HSet.notMem_empty a.1 a.2⟩

/-- The fibre at `{∅}` contains the actual empty set with its membership. -/
def singletonFibreValue :
    memberOfMemberFamily.{u} (memberEquiv emptySingletonBase singletonIndex) :=
  ⟨∅, HSet.mem_singleton_self ∅⟩

/-- The two fibres are not equivalent; the dependent comparison really
handles a nonconstant family. -/
theorem memberOfMemberFamily_fibres_not_equiv :
    ¬ Nonempty (memberOfMemberFamily.{u} (memberEquiv emptySingletonBase emptyIndex) ≃
      memberOfMemberFamily (memberEquiv emptySingletonBase singletonIndex)) := by
  rintro ⟨e⟩
  exact isEmptyElim (e.symm singletonFibreValue)

/-- A dependent pair carrying the member of `{∅}` keeps its complete result
when the well-founded base index is included into the ambient carrier. -/
theorem singletonFibreValue_preserved :
    ((memberSigmaEquiv emptySingletonBase memberOfMemberFamily).toFun
      ⟨singletonIndex, singletonFibreValue⟩).2 = singletonFibreValue :=
  memberSigmaEquiv_value emptySingletonBase memberOfMemberFamily _

/-- A section cannot select a member in every fibre: the `∅` fibre is empty. -/
theorem no_memberOfMember_section :
    ¬ Nonempty ((a : El Mem emptySingletonBase.{u}) →
      memberOfMemberFamily (memberEquiv emptySingletonBase a)) := by
  rintro ⟨s⟩
  exact isEmptyElim (s emptyIndex)

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
