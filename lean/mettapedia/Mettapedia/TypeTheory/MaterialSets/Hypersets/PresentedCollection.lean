import Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialDecoder

/-!
# Constructed dependent collection in the generated material model

Presented domains and fibres construct the material set of every relation
witness, at their common graph bound. Rows retain their dependent index.
Strong typed collection follows without choosing one witness per index.
For a total functional relation a bounded separation-and-union operation
computes the unique encoded witness and decodes an actual section.

All presentation and decoding data are instantiated by the generated-core
interpreter. This establishes typed collection and unique replacement for
that concrete model. It does not identify them with unrestricted same-level
collection over the entire bare hyperset carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedCollection

open AccessiblePointedGraph

universe u

variable {A : Type u} {B : A → Type u}
variable (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))
variable (relation : (a : A) → B a → Prop)

abbrev Witness := Σ a : A, {b : B a // relation a b}

def rowGraph (witness : Witness relation) : AccessiblePointedGraph.{u} :=
  kpairGraph (domain.termGraph witness.1) ((fibres witness.1).termGraph witness.2.val)

theorem mk_rowGraph (witness : Witness relation) : HSet.mk (rowGraph domain fibres relation witness) =
    HSet.kpair (domain.value witness.1) ((fibres witness.1).value witness.2.val) := by
  rw [rowGraph, mk_kpairGraph, PresentedType.mk_termGraph, PresentedType.mk_termGraph]

/-- Every witness is retained; no collecting carrier is supplied. -/
def graph : AccessiblePointedGraph.{u} := sup (rowGraph domain fibres relation)

def rows : HSet.{u} := HSet.mk (graph domain fibres relation)

theorem mem_rows (value : HSet.{u}) : value ∈ rows domain fibres relation ↔
    ∃ a : A, ∃ b : B a, relation a b ∧
      HSet.kpair (domain.value a) ((fibres a).value b) = value := by
  rw [rows]
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, same⟩ := HSet.mem_range.mp member
    exact ⟨a, b.val, b.property, (mk_rowGraph domain fibres relation ⟨a, b⟩).symm.trans same⟩
  · rintro ⟨a, b, related, same⟩
    exact HSet.mem_range.mpr ⟨⟨a, b, related⟩,
      (mk_rowGraph domain fibres relation ⟨a, b, related⟩).trans same⟩

/-- Exact dependent rows retain the input identity as well as the output. -/
theorem pair_mem_rows (a : A) (b : B a) :
    HSet.kpair (domain.value a) ((fibres a).value b) ∈ rows domain fibres relation ↔ relation a b := by
  constructor
  · intro member
    obtain ⟨a', b', related, same⟩ := (mem_rows domain fibres relation _).mp member
    have firstSame : a' = a := domain.value_injective (HSet.kpair_inj.mp same).1
    cases firstSame
    have secondSame : b' = b := (fibres a).value_injective (HSet.kpair_inj.mp same).2
    exact secondSame ▸ related
  · intro related
    exact (mem_rows domain fibres relation _).mpr ⟨a, b, related, rfl⟩

/-- The constructed rows prove both strong-collection clauses for the whole
actual relation. Totality is a logical property of the input relation. -/
theorem strong_collection (total : ∀ a, ∃ b, relation a b) :
    (∀ a, ∃ b, relation a b ∧
      HSet.kpair (domain.value a) ((fibres a).value b) ∈ rows domain fibres relation) ∧
    (∀ value, value ∈ rows domain fibres relation →
      ∃ a b, relation a b ∧ HSet.kpair (domain.value a) ((fibres a).value b) = value) := by
  constructor
  · intro a
    obtain ⟨b, related⟩ := total a
    exact ⟨b, related, (pair_mem_rows domain fibres relation a b).mpr related⟩
  · intro value member
    exact (mem_rows domain fibres relation value).mp member

/-- Typed replacement needs no quotient representative or global
unique-description principle: union decodes the bounded singleton fibre. -/
def witnessValue (a : A) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun value =>
    HSet.kpair (domain.value a) value ∈ rows domain fibres relation) (fibres a).carrier)

theorem witnessValue_eq (functional : ∀ a b first, relation a b → relation a first → b = first)
    (a : A) (b : B a) (related : relation a b) :
    witnessValue domain fibres relation a = (fibres a).value b := by
  have singleton : HSet.sep (fun value =>
      HSet.kpair (domain.value a) value ∈ rows domain fibres relation) (fibres a).carrier =
      {(fibres a).value b} := by
    apply HSet.ext
    intro value
    rw [HSet.mem_sep, HSet.mem_singleton]
    constructor
    · rintro ⟨member, row⟩
      let first := (fibres a).decode ⟨value, member⟩
      have firstValue : (fibres a).value first = value := (fibres a).value_decode _
      have firstRelated : relation a first := (pair_mem_rows domain fibres relation a first).mp
        (firstValue.symm ▸ row)
      exact firstValue.symm.trans (congrArg (fibres a).value (functional a first b firstRelated related))
    · intro same
      exact ⟨same.symm ▸ (fibres a).value_mem b,
        same.symm ▸ (pair_mem_rows domain fibres relation a b).mpr related⟩
  rw [witnessValue, singleton, HSet.sUnion_singleton]

/-- Both existence and uniqueness are discharged by the actual bounded
material computation. The hypotheses specify the authored relation. -/
def uniqueSection (total : ∀ a, ∃ b, relation a b)
    (functional : ∀ a b first, relation a b → relation a first → b = first) : (a : A) → B a :=
  fun a => (fibres a).decode ⟨witnessValue domain fibres relation a, by
    obtain ⟨b, related⟩ := total a
    rw [witnessValue_eq domain fibres relation functional a b related]
    exact (fibres a).value_mem b⟩

theorem uniqueSection_eq (total : ∀ a, ∃ b, relation a b)
    (functional : ∀ a b first, relation a b → relation a first → b = first)
    (a : A) (b : B a) (related : relation a b) :
    uniqueSection domain fibres relation total functional a = b := by
  apply (fibres a).value_injective
  exact ((fibres a).value_decode _).trans
    (witnessValue_eq domain fibres relation functional a b related)

theorem uniqueSection_spec (total : ∀ a, ∃ b, relation a b)
    (functional : ∀ a b first, relation a b → relation a first → b = first) (a : A) :
    relation a (uniqueSection domain fibres relation total functional a) := by
  obtain ⟨b, related⟩ := total a
  rw [uniqueSection_eq domain fibres relation total functional a b related]
  exact related

theorem uniqueSection_unique (total : ∀ a, ∃ b, relation a b)
    (functional : ∀ a b first, relation a b → relation a first → b = first)
    (sectionValue : (a : A) → B a) (satisfies : ∀ a, relation a (sectionValue a)) :
    sectionValue = uniqueSection domain fibres relation total functional := by
  funext a
  exact (uniqueSection_eq domain fibres relation total functional a (sectionValue a) (satisfies a)).symm

theorem rows_false : rows domain fibres (fun _ _ => False) = (∅ : HSet.{u}) := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨_, _, impossible, _⟩ := (mem_rows domain fibres _ value).mp member
  exact impossible

/-- Without functionality, this operation collects the entire output fibre
and computes its union. There is no arbitrary witness selection. -/
theorem witnessValue_all (a : A) :
    witnessValue domain fibres (fun _ _ => True) a = HSet.sUnion (fibres a).carrier := by
  unfold witnessValue
  congr 1
  apply HSet.ext
  intro value
  rw [HSet.mem_sep]
  constructor
  · exact And.left
  · intro member
    refine ⟨member, ?_⟩
    have encoded : (fibres a).value ((fibres a).decode ⟨value, member⟩) = value :=
      (fibres a).value_decode _
    exact encoded ▸ (pair_mem_rows domain fibres (fun _ _ => True) a _).mpr trivial

section GeneratedInstantiation

open GeneratedMaterialDecoder LiftedFamilyModel

variable {X : HSet.{u}} {Family : Elements X → HSet.{u}}
variable {S : Type (u + 1)} {T : S → Type (u + 1)}
variable (sourceCode : CoreGeneration (Elements X) (fun a => Elements (Family a)) S)
variable (targetCode : (source : S) → CoreGeneration (Elements X) (fun a => Elements (Family a)) (T source))
variable (typedRelation : (source : S) → T source → Prop)

/-- Every model and graph in the collecting construction is now constructed
from the original bare family and the whole generated grammar. -/
def generatedRows : HSet.{u + 1} :=
  rows (interpretFamily X Family sourceCode)
    (fun source => interpretFamily X Family (targetCode source)) typedRelation

theorem generatedRows_exact (value : HSet.{u + 1}) : value ∈ generatedRows sourceCode targetCode typedRelation ↔
    ∃ source result, typedRelation source result ∧
      HSet.kpair ((interpretFamily X Family sourceCode).value source)
        ((interpretFamily X Family (targetCode source)).value result) = value :=
  mem_rows _ _ _ value

/-- The actual unique section exists throughout arbitrarily nested dependent
Π/Σ/Id/W families at their one common material bound. -/
def generatedUniqueSection (total : ∀ source, ∃ result, typedRelation source result)
    (functional : ∀ source first second,
      typedRelation source first → typedRelation source second → first = second) : (source : S) → T source :=
  uniqueSection (interpretFamily X Family sourceCode)
    (fun source => interpretFamily X Family (targetCode source)) typedRelation total functional

theorem generatedUniqueSection_spec (total : ∀ source, ∃ result, typedRelation source result)
    (functional : ∀ source first second,
      typedRelation source first → typedRelation source second → first = second) (source : S) :
    typedRelation source (generatedUniqueSection sourceCode targetCode typedRelation total functional source) :=
  uniqueSection_spec _ _ _ _ _ source

end GeneratedInstantiation

section Controls

open GeneratedMaterialDecoder LiftedFamilyModel

def singletonFamily (X : HSet.{u}) (member : Elements X) : HSet.{u} := {member.1}

private theorem singletonTotal (X : HSet.{u}) (member : Elements X) :
    ∃ _result : Elements (singletonFamily X member), True :=
  ⟨⟨member.1, HSet.mem_singleton.mpr rfl⟩, trivial⟩

private theorem singletonFunctional (X : HSet.{u}) (member : Elements X)
    (first second : Elements (singletonFamily X member)) (_ : True) (_ : True) : first = second :=
  Mettapedia.TypeTheory.MaterialSets.El.ext HSet.propositional
    ((HSet.mem_singleton.mp first.2).trans (HSet.mem_singleton.mp second.2).symm)

/-- A genuinely index-dependent family has its compatible section computed
from typed totality and functionality at every original material base. -/
def singletonSection (X : HSet.{u}) : (member : Elements X) → Elements (singletonFamily X member) :=
  generatedUniqueSection (Family := singletonFamily X) .base .fibre (fun _ _ => True)
    (singletonTotal X) (singletonFunctional X)

theorem singletonSection_beta (X : HSet.{u}) (member : Elements X) :
    singletonSection X member = ⟨member.1, HSet.mem_singleton.mpr rfl⟩ := by
  unfold singletonSection generatedUniqueSection
  exact uniqueSection_eq _ _ (fun _ _ => True) (singletonTotal X) (singletonFunctional X)
    member _ trivial

def nonfunctionalCarrier : HSet.{u} := {({∅} : HSet.{u}), {{∅}}}

private theorem union_not_member : HSet.sUnion nonfunctionalCarrier.{u} ∉ nonfunctionalCarrier := by
  have zeroMember : (∅ : HSet.{u}) ∈ HSet.sUnion nonfunctionalCarrier :=
    HSet.mem_sUnion.mpr ⟨{∅}, HSet.mem_pair.mpr (Or.inl rfl), HSet.mem_singleton_self _⟩
  have oneMember : ({∅} : HSet.{u}) ∈ HSet.sUnion nonfunctionalCarrier :=
    HSet.mem_sUnion.mpr ⟨{{∅}}, HSet.mem_pair.mpr (Or.inr rfl), HSet.mem_singleton_self _⟩
  intro member
  rcases HSet.mem_pair.mp member with same | same
  · rw [same] at oneMember
    exact HSet.empty_ne_singleton_empty (HSet.mem_singleton.mp oneMember).symm
  · rw [same] at zeroMember
    exact HSet.empty_ne_singleton_empty (HSet.mem_singleton.mp zeroMember)

/-- Totality alone does not justify the unique-section decoder: in this
actual model the union of the witness fibre is not even a fibre member. -/
theorem totality_without_functionality_fails :
    witnessValue PresentedType.unit
      (fun _ : ULift.{u + 1, 0} PUnit => liftedModel nonfunctionalCarrier.{u})
      (fun _ _ => True) (ULift.up PUnit.unit) ∉ (liftedModel nonfunctionalCarrier.{u}).carrier := by
  rw [witnessValue_all]
  change HSet.sUnion (HSet.mk (HSet.presentationUp nonfunctionalCarrier.{u})) ∉
    HSet.mk (HSet.presentationUp nonfunctionalCarrier.{u})
  rw [HSet.mk_presentationUp, ← HSet.lift_sUnion, HSet.lift_mem_lift_iff]
  exact union_not_member

end Controls

#print axioms strong_collection
#print axioms uniqueSection
#print axioms uniqueSection_spec
#print axioms generatedRows_exact
#print axioms generatedUniqueSection_spec
#print axioms singletonSection_beta
#print axioms totality_without_functionality_fails

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedCollection
