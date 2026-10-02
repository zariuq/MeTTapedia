import Mettapedia.Logic.TheoryModel.IdentityProofs
import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Carving a universe, and the h-set carve of identity

**Carving.**  The fragment of a universe `U` cut out by axioms `Φ` is
`carve Sat U Φ = U ∩ models Sat Φ`.  Computing consequences in the carved fragment
is computing them in `U` with `Φ` added (`consequencesIn_carve`).  Consequences in a
universe form a closure operator on theories (`consequencesInClosure`); theories
closed in a carved fragment are closed in the ambient universe
(`consequencesIn_eq_of_carve`), and they form a **Galois insertion** into the
ambient closed theories whose reflector adds `Φ` and closes (`carveInsertion`).  A
carved fragment is thus a reflective part of the ambient theory lattice.

**The h-set carve of identity.**  In the signature of identity proofs:

* the **groupoid-valued universe** `groupoidUniverse` is the class of all models of
  the groupoid laws; it hosts them faithfully;
* its **h-set fragment** `hsetFragment`, carved by `uip` (all parallel proofs
  equal), is exactly the class of models of `uipLaws` (`hsetFragment_eq`) and
  validates exactly the consequences of `uipLaws`
  (`consequencesIn_hsetFragment`), namely every sentence except `connected`;
* the reflector of the carve sends the closed theory `groupoidLaws` to exactly the
  theory of `uipLaws` (`hsetReflection_groupoidLaws`);
* **faithful hosting of the identity theory forces leaving the h-set fragment**: a
  universe of thin structures never hosts the groupoid laws faithfully
  (`not_hostsFaithfully_of_subset_thin`).

**Mathlib groupoids.**  Every Mathlib groupoid is a model of the groupoid laws
(`ofGroupoid_mem_groupoidUniverse`); it satisfies `uip` exactly when it is thin
(`ofGroupoid_sat_uip_iff`).  The universe of small Mathlib groupoids hosts the
groupoid laws faithfully (`hostsFaithfully_groupoidValued`) and its h-set carve,
the thin groupoids, validates exactly the `uipLaws` consequences.

**Presheaves: extensional identity, and the combination.**  In a presheaf topos a
predicate is a subfunctor, and the identity of a presheaf `X` is the diagonal
subfunctor of `X × X` (`diagonal`).  The identity structure it gives at any stage
(`presheafIdentity`) is thin, so the universe of these structures lies in the h-set
fragment and does not host the groupoid laws faithfully
(`not_hostsFaithfully_presheafIdentities`).  Presheaves valued in groupoids have the
stage identities `ofGroupoid (X.obj c)`; over any category with an object they host
the groupoid laws faithfully (`hostsFaithfully_groupoidPresheaves`).  Univalence
itself needs more than groupoid values (a model structure: cubical or simplicial);
that is not formalised here.

**Controls.**  `xorModel` (two parallel proofs), `dihedralModel`, the univalent
structure `univalentModel` and the Mathlib groupoid with a non-trivial loop
`xorGroupoidModel` are groupoidal and outside the h-set fragment; `eqModel` is
inside; `badModel` is not groupoidal.  The univalent universe of propositions,
`propUnivalentModel` (subsingleton types with equivalences), is thin, while the
univalent universe of all types is not.

The carve theorems and the identity instance use only `propext` and `Quot.sound`
elementwise; the closure-operator and Galois-insertion packaging inherits
`Classical.choice` from Mathlib's order on `Set`, and the groupoid-valued
presheaves inherit it from Mathlib's category of groupoids and constant functors.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set

universe uStr uSent

/-! ## Carving a universe -/

section Carve

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-- **The fragment of a universe carved out by axioms `Φ`.** -/
def carve (U : Set Str) (Φ : Set Sent) : Set Str :=
  U ∩ models Sat Φ

variable {Sat}

theorem carve_subset (U : Set Str) (Φ : Set Sent) : carve Sat U Φ ⊆ U :=
  fun _ member => member.1

theorem mem_carve {U : Set Str} {Φ : Set Sent} {m : Str} :
    m ∈ carve Sat U Φ ↔ m ∈ U ∧ m ∈ models Sat Φ :=
  Iff.rfl

/-- The models hosted by a carved fragment are the models of the enlarged theory
hosted by the universe. -/
theorem modelsIn_carve (U : Set Str) (Φ T : Set Sent) :
    modelsIn Sat (carve Sat U Φ) T = modelsIn Sat U (Φ ∪ T) := by
  ext m
  constructor
  · rintro ⟨⟨hosted, modelΦ⟩, modelT⟩
    exact ⟨hosted, fun _ member => member.elim (fun inΦ => modelΦ inΦ) fun inT => modelT inT⟩
  · rintro ⟨hosted, model⟩
    exact ⟨⟨hosted, fun _ inΦ => model (Or.inl inΦ)⟩, fun _ inT => model (Or.inr inT)⟩

/-- **Carving computes the consequences of the enlarged theory.** -/
theorem consequencesIn_carve (U : Set Str) (Φ T : Set Sent) :
    consequencesIn Sat (carve Sat U Φ) T = consequencesIn Sat U (Φ ∪ T) := by
  rw [consequencesIn, consequencesIn, modelsIn_carve]

/-- A carved fragment validates at least what its universe validates. -/
theorem consequencesIn_subset_carve (U : Set Str) (Φ T : Set Sent) :
    consequencesIn Sat U T ⊆ consequencesIn Sat (carve Sat U Φ) T :=
  consequencesIn_anti (carve_subset U Φ) T

theorem consequencesIn_mono_theory (U : Set Str) {T T' : Set Sent} (included : T ⊆ T') :
    consequencesIn Sat U T ⊆ consequencesIn Sat U T' :=
  theoryOf_anti (modelsIn_anti_theory U included)

theorem consequencesIn_idem (U : Set Str) (T : Set Sent) :
    consequencesIn Sat U (consequencesIn Sat U T) = consequencesIn Sat U T := by
  apply Subset.antisymm
  · exact theoryOf_anti fun _ hosted => ⟨hosted.1, fun _ member => member hosted⟩
  · exact subset_consequencesIn U _

/-- **Theories closed in a carved fragment are closed in the ambient universe.** -/
theorem consequencesIn_eq_of_carve {U : Set Str} {Φ T : Set Sent}
    (closed : consequencesIn Sat (carve Sat U Φ) T = T) : consequencesIn Sat U T = T := by
  apply Subset.antisymm _ (subset_consequencesIn U T)
  intro φ validated
  rw [← closed]
  exact consequencesIn_subset_carve U Φ T validated

variable (Sat)

/-- Consequences computed in a universe, as a closure operator on theories. -/
def consequencesInClosure (U : Set Str) : ClosureOperator (Set Sent) where
  toFun := consequencesIn Sat U
  monotone' _ _ included := consequencesIn_mono_theory U included
  le_closure' := subset_consequencesIn U
  idempotent' := consequencesIn_idem U

theorem isClosed_consequencesInClosure_iff {U : Set Str} {T : Set Sent} :
    (consequencesInClosure Sat U).IsClosed T ↔ consequencesIn Sat U T = T :=
  (consequencesInClosure Sat U).isClosed_iff

/-- A closed theory of a carved fragment, as a closed theory of the universe. -/
def carveClosedInclusion (U : Set Str) (Φ : Set Sent)
    (T : (consequencesInClosure Sat (carve Sat U Φ)).Closeds) :
    (consequencesInClosure Sat U).Closeds :=
  ⟨T.1, (isClosed_consequencesInClosure_iff Sat).mpr
    (consequencesIn_eq_of_carve ((isClosed_consequencesInClosure_iff Sat).mp T.2))⟩

/-- **Carving is a Galois insertion of theories.**  The closed theories of the
carved fragment are a reflective part of the closed theories of the universe; the
reflector closes a theory in the fragment, that is, adds `Φ` and closes. -/
def carveInsertion (U : Set Str) (Φ : Set Sent) :
    GaloisInsertion
      (fun T : (consequencesInClosure Sat U).Closeds =>
        (consequencesInClosure Sat (carve Sat U Φ)).toCloseds T.1)
      (carveClosedInclusion Sat U Φ) :=
  GaloisConnection.toGaloisInsertion (fun _ T' => T'.2.closure_le_iff)
    (fun T' => (consequencesInClosure Sat (carve Sat U Φ)).le_closure T'.1)

theorem carveInsertion_reflect (U : Set Str) (Φ : Set Sent)
    (T : (consequencesInClosure Sat U).Closeds) :
    ((consequencesInClosure Sat (carve Sat U Φ)).toCloseds T.1).1 =
      consequencesIn Sat U (Φ ∪ T.1) :=
  consequencesIn_carve U Φ T.1

end Carve

/-! ## The h-set carve of identity -/

namespace IdentityProofs

universe u v w uC vC

/-- **The groupoid-valued universe**: every structure satisfying the groupoid
laws. -/
def groupoidUniverse : Set IdStructure.{u} :=
  models IdStructure.Sat groupoidLaws

/-- **The h-set fragment**: the groupoid-valued universe carved by `uip`. -/
def hsetFragment : Set IdStructure.{u} :=
  carve IdStructure.Sat groupoidUniverse {IdSentence.uip}

/-- The thin structures are the models of `uip`. -/
theorem thin_eq_models_uip : thin.{u} = models IdStructure.Sat {IdSentence.uip} := by
  ext M
  constructor
  · intro uip φ member
    change φ = IdSentence.uip at member
    subst member
    exact uip
  · intro model
    exact model rfl

theorem mem_hsetFragment_iff {M : IdStructure.{u}} :
    M ∈ hsetFragment ↔ M ∈ models IdStructure.Sat uipLaws := by
  constructor
  · rintro ⟨groupoid, uip⟩
    intro φ member
    rcases member with equal | law
    · exact uip equal
    · exact groupoid law
  · intro model
    exact ⟨models_anti groupoidLaws_subset_uipLaws model, fun φ equal => model (Or.inl equal)⟩

/-- **The h-set fragment is exactly the class of models of `uipLaws`.** -/
theorem hsetFragment_eq : hsetFragment.{u} = models IdStructure.Sat uipLaws :=
  Set.ext fun _ => mem_hsetFragment_iff

theorem hsetFragment_subset_thin : hsetFragment.{u} ⊆ thin :=
  fun _ member => member.2 rfl

theorem hsetFragment_subset_groupoidUniverse : hsetFragment.{u} ⊆ groupoidUniverse :=
  carve_subset _ _

/-- The groupoid-valued universe hosts the groupoid laws faithfully. -/
theorem hostsFaithfully_groupoidUniverse :
    HostsFaithfully IdStructure.Sat groupoidUniverse.{u} groupoidLaws := by
  apply hostsFaithfully_iff_subset.mpr
  intro φ validated M model
  exact validated ⟨model, model⟩

/-- `groupoidLaws` is closed in the groupoid-valued universe. -/
theorem consequencesIn_groupoidUniverse :
    consequencesIn IdStructure.Sat groupoidUniverse.{u} groupoidLaws = groupoidLaws :=
  hostsFaithfully_groupoidUniverse.trans consequences_groupoidLaws

/-- **The h-set fragment validates exactly the theory of `uipLaws`.** -/
theorem consequencesIn_hsetFragment :
    consequencesIn IdStructure.Sat hsetFragment.{u} groupoidLaws =
      theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop)
        (models IdStructure.Sat uipLaws) := by
  apply Subset.antisymm
  · intro φ validated M model
    exact validated ⟨mem_hsetFragment_iff.mpr model,
      models_anti groupoidLaws_subset_uipLaws model⟩
  · intro φ entailed M hosted
    exact entailed (mem_hsetFragment_iff.mp hosted.1)

/-- Explicitly: every sentence except `connected`. -/
theorem consequencesIn_hsetFragment_eq :
    consequencesIn IdStructure.Sat hsetFragment.{u} groupoidLaws = {φ | φ ≠ .connected} :=
  consequencesIn_hsetFragment.trans consequences_uipLaws.{u}

/-- The h-set fragment does not host the groupoid laws faithfully. -/
theorem not_hostsFaithfully_hsetFragment :
    ¬ HostsFaithfully IdStructure.Sat hsetFragment.{u} groupoidLaws := by
  apply not_hostsFaithfully_of (φ := .uip)
  · rw [consequencesIn_hsetFragment_eq]
    exact fun equal => IdSentence.noConfusion equal
  · exact not_entails_uip

/-- **Faithful hosting of the identity theory forces leaving the h-set
fragment**: no universe of thin structures hosts the groupoid laws faithfully. -/
theorem not_hostsFaithfully_of_subset_thin {U : Set IdStructure.{u}} (inside : U ⊆ thin) :
    ¬ HostsFaithfully IdStructure.Sat U groupoidLaws :=
  not_hostsFaithfully_of (φ := .uip) (fun _ hosted => inside hosted.1) not_entails_uip

/-- `groupoidLaws` as a closed theory of the groupoid-valued universe. -/
def groupoidLawsClosed :
    (consequencesInClosure IdStructure.Sat groupoidUniverse.{u}).Closeds :=
  ⟨groupoidLaws, (isClosed_consequencesInClosure_iff _).mpr consequencesIn_groupoidUniverse⟩

/-- **The h-set carve as a Galois insertion.** -/
def hsetInsertion :=
  carveInsertion IdStructure.Sat groupoidUniverse.{u} {IdSentence.uip}

/-- **The reflector of the h-set carve sends the groupoid laws to exactly the
theory of `uipLaws`.** -/
theorem hsetReflection_groupoidLaws :
    ((consequencesInClosure IdStructure.Sat hsetFragment.{u}).toCloseds
        groupoidLawsClosed.{u}.1).1 =
      theoryOf (IdStructure.Sat : IdStructure.{u} → IdSentence → Prop)
        (models IdStructure.Sat uipLaws) :=
  consequencesIn_hsetFragment

/-! ### Controls -/

theorem xorModel_mem_groupoidUniverse : xorModel.{u} ∈ groupoidUniverse :=
  xorModel_mem_groupoidLaws

/-- A groupoid with two parallel proofs is outside the h-set fragment. -/
theorem xorModel_not_mem_hsetFragment : xorModel.{u} ∉ hsetFragment :=
  fun member => xorModel_not_uip (hsetFragment_subset_thin member)

theorem eqModel_mem_hsetFragment (α : Type u) : eqModel α ∈ hsetFragment :=
  mem_hsetFragment_iff.mpr (eqModel_mem_uipLaws α)

theorem dihedralModel_not_mem_hsetFragment : dihedralModel.{u} ∉ hsetFragment :=
  fun member => dihedralModel_not_loopComm
    (IdStructure.sat_loopComm_of_uip (hsetFragment_subset_thin member))

theorem badModel_not_mem_groupoidUniverse : badModel.{u} ∉ groupoidUniverse :=
  badModel_not_model

theorem univalentModel_mem_groupoidUniverse : univalentModel ∈ groupoidUniverse :=
  univalentModel_mem_groupoidLaws

/-- The univalent structure of all types, with its non-trivial loop `notEquiv`, is
outside the h-set fragment. -/
theorem univalentModel_not_mem_hsetFragment : univalentModel ∉ hsetFragment :=
  fun member => univalentModel_not_uip (hsetFragment_subset_thin member)

/-- The univalent universe of propositions: subsingleton types, with equivalences as
identity proofs. -/
def propUnivalentModel : IdStructure.{1} where
  Pt := {A : Type // Subsingleton A}
  Pf A B := ULift.{1} (A.1 ≃ B.1)
  refl A := ⟨Equiv.refl A.1⟩
  inv p := ⟨p.down.symm⟩
  comp p q := ⟨p.down.trans q.down⟩

/-- **The univalent universe of propositions is thin**: two equivalences between
subsingleton types agree. -/
theorem propUnivalentModel_sat_uip : propUnivalentModel.Sat .uip := by
  intro _ B p q
  exact congrArg ULift.up (equiv_eq fun _ => @Subsingleton.elim _ B.2 _ _)

theorem propUnivalentModel_mem_hsetFragment : propUnivalentModel ∈ hsetFragment := by
  have uip : propUnivalentModel.Sat .uip := propUnivalentModel_sat_uip
  refine mem_hsetFragment_iff.mpr ?_
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact uip
  · exact fun _ _ _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _

/-! ## Mathlib groupoids -/

section MathlibGroupoids

open CategoryTheory

/-- **A Mathlib groupoid as an identity structure**: objects as points, morphisms as
proofs. -/
def ofGroupoid (G : Type w) [Groupoid.{v} G] : IdStructure.{max w v} where
  Pt := ULift.{v} G
  Pf a b := ULift.{w} (a.down ⟶ b.down)
  refl a := ⟨𝟙 a.down⟩
  inv p := ⟨Groupoid.inv p.down⟩
  comp p q := ⟨p.down ≫ q.down⟩

/-- Every Mathlib groupoid satisfies the groupoid laws. -/
theorem ofGroupoid_mem_groupoidUniverse (G : Type w) [Groupoid.{v} G] :
    ofGroupoid G ∈ groupoidUniverse :=
  mem_models_groupoidLaws
    (fun p q r => congrArg ULift.up (Category.assoc p.down q.down r.down))
    (fun p => congrArg ULift.up (Category.id_comp p.down))
    (fun p => congrArg ULift.up (Category.comp_id p.down))
    (fun p => congrArg ULift.up (Groupoid.inv_comp p.down))
    (fun p => congrArg ULift.up (Groupoid.comp_inv p.down))

/-- **A Mathlib groupoid satisfies `uip` exactly when it is thin.** -/
theorem ofGroupoid_sat_uip_iff (G : Type w) [Groupoid.{v} G] :
    (ofGroupoid G).Sat .uip ↔ Quiver.IsThin G := by
  constructor
  · intro uip a b
    exact ⟨fun p q => congrArg ULift.down (@uip ⟨a⟩ ⟨b⟩ ⟨p⟩ ⟨q⟩)⟩
  · intro thin _ _ p q
    exact congrArg ULift.up (Subsingleton.elim p.down q.down)

/-- The one-object groupoid of a loop algebra satisfying the group laws. -/
abbrev loopGroupoid (L : Type) (unit : L) (inv : L → L) (mul : L → L → L)
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)) (unit_mul : ∀ x, mul unit x = x)
    (mul_unit : ∀ x, mul x unit = x) (inv_mul : ∀ x, mul (inv x) x = unit)
    (mul_inv : ∀ x, mul x (inv x) = unit) : Groupoid.{0} PUnit.{1} where
  Hom _ _ := L
  id _ := unit
  comp p q := mul p q
  id_comp p := unit_mul p
  comp_id p := mul_unit p
  assoc p q r := assoc p q r
  inv p := inv p
  inv_comp p := inv_mul p
  comp_inv p := mul_inv p

/-- Two loops composing by exclusive or. -/
abbrev xorGroupoid : Groupoid.{0} PUnit.{1} :=
  loopGroupoid Bool false id xor
    (fun x y z => by cases x <;> cases y <;> cases z <;> rfl)
    (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)

/-- The symmetries of a triangle as loops. -/
abbrev dihedralGroupoid : Groupoid.{0} PUnit.{1} :=
  loopGroupoid D3 D3.one D3.inv D3.mul D3.mul_assoc D3.one_mul D3.mul_one D3.inv_mul D3.mul_inv

/-- **A Mathlib groupoid with a non-trivial loop.** -/
def xorGroupoidModel : IdStructure.{0} :=
  @ofGroupoid.{0, 0} PUnit.{1} xorGroupoid

def dihedralGroupoidModel : IdStructure.{0} :=
  @ofGroupoid.{0, 0} PUnit.{1} dihedralGroupoid

/-- Two points and no morphism between different points. -/
def discreteBoolModel : IdStructure.{0} :=
  ofGroupoid.{0, 0} (Discrete Bool)

theorem xorGroupoidModel_not_uip : ¬ xorGroupoidModel.Sat .uip := by
  intro uip
  exact Bool.noConfusion (congrArg (fun p : ULift.{0} Bool => p.down)
    (@uip ⟨PUnit.unit⟩ ⟨PUnit.unit⟩ ⟨false⟩ ⟨true⟩))

theorem dihedralGroupoidModel_not_loopComm : ¬ dihedralGroupoidModel.Sat .loopComm := by
  intro comm
  exact D3.not_comm (congrArg (fun p : ULift.{0} D3 => p.down)
    (@comm ⟨PUnit.unit⟩ ⟨⟨.r1, false⟩⟩ ⟨⟨.r0, true⟩⟩))

theorem discreteBoolModel_not_connected : ¬ discreteBoolModel.Sat .connected := by
  intro connected
  obtain ⟨⟨⟨⟨equal⟩⟩⟩⟩ := connected ⟨⟨true⟩⟩ ⟨⟨false⟩⟩
  exact Bool.noConfusion equal

theorem discreteBoolModel_sat_uip : discreteBoolModel.Sat .uip := by
  intro _ _ p q
  obtain ⟨⟨⟨_⟩⟩⟩ := p
  obtain ⟨⟨⟨_⟩⟩⟩ := q
  rfl

/-- **The universe of small Mathlib groupoids.** -/
def groupoidValued : Set IdStructure.{0} :=
  {M | ∃ (G : Type) (_ : Groupoid.{0} G), M = ofGroupoid G}

theorem groupoidValued_subset_groupoidUniverse : groupoidValued ⊆ groupoidUniverse.{0} := by
  rintro _ ⟨G, _, rfl⟩
  exact ofGroupoid_mem_groupoidUniverse G

theorem xorGroupoidModel_mem : xorGroupoidModel ∈ groupoidValued :=
  ⟨PUnit.{1}, xorGroupoid, rfl⟩

theorem dihedralGroupoidModel_mem : dihedralGroupoidModel ∈ groupoidValued :=
  ⟨PUnit.{1}, dihedralGroupoid, rfl⟩

theorem discreteBoolModel_mem : discreteBoolModel ∈ groupoidValued :=
  ⟨Discrete Bool, inferInstance, rfl⟩

/-- **The universe of small Mathlib groupoids hosts the groupoid laws
faithfully.** -/
theorem hostsFaithfully_groupoidValued :
    HostsFaithfully IdStructure.Sat groupoidValued groupoidLaws := by
  apply hostsFaithfully_iff_subset.mpr
  rw [consequences_groupoidLaws]
  intro φ validated
  cases φ with
  | uip =>
      exact (xorGroupoidModel_not_uip (validated ⟨xorGroupoidModel_mem,
        groupoidValued_subset_groupoidUniverse xorGroupoidModel_mem⟩)).elim
  | loopComm =>
      exact (dihedralGroupoidModel_not_loopComm (validated ⟨dihedralGroupoidModel_mem,
        groupoidValued_subset_groupoidUniverse dihedralGroupoidModel_mem⟩)).elim
  | connected =>
      exact (discreteBoolModel_not_connected (validated ⟨discreteBoolModel_mem,
        groupoidValued_subset_groupoidUniverse discreteBoolModel_mem⟩)).elim
  | assoc => exact Or.inl rfl
  | leftUnit => exact Or.inr (Or.inl rfl)
  | rightUnit => exact Or.inr (Or.inr (Or.inl rfl))
  | leftInv => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | rightInv => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- **The thin Mathlib groupoids validate exactly the `uipLaws` consequences.** -/
theorem consequencesIn_carve_groupoidValued :
    consequencesIn IdStructure.Sat (carve IdStructure.Sat groupoidValued {IdSentence.uip})
        groupoidLaws = {φ | φ ≠ .connected} := by
  ext φ
  constructor
  · intro validated equal
    subst equal
    exact discreteBoolModel_not_connected (validated ⟨⟨discreteBoolModel_mem,
      fun _ equal => equal ▸ discreteBoolModel_sat_uip⟩,
      groupoidValued_subset_groupoidUniverse discreteBoolModel_mem⟩)
  · intro notConnected M hosted
    have uipLawsModel : M ∈ models IdStructure.Sat uipLaws :=
      mem_hsetFragment_iff.mp ⟨groupoidValued_subset_groupoidUniverse hosted.1.1, hosted.1.2⟩
    have entailed : φ ∈ theoryOf IdStructure.Sat (models IdStructure.Sat uipLaws) := by
      rw [consequences_uipLaws]
      exact notConnected
    exact entailed uipLawsModel

theorem xorGroupoidModel_not_mem_carve :
    xorGroupoidModel ∉ carve IdStructure.Sat groupoidValued {IdSentence.uip} :=
  fun member => xorGroupoidModel_not_uip (member.2 rfl)

end MathlibGroupoids

/-! ## Presheaves: the identity predicate is extensional -/

section PresheafIdentity

open CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/-- The presheaf of pairs of elements of `X`. -/
def pairPresheaf (X : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj c := X.obj c × X.obj c
  map f := TypeCat.ofHom fun p => (X.map f p.1, X.map f p.2)
  map_id c := by
    ext p
    · exact Functor.map_id_apply X c p.1
    · exact Functor.map_id_apply X c p.2
  map_comp f g := by
    ext p
    · exact Functor.map_comp_apply X f g p.1
    · exact Functor.map_comp_apply X f g p.2

/-- **The identity predicate of a presheaf**: the diagonal, a subfunctor of the
pairs. -/
def diagonal (X : Cᵒᵖ ⥤ Type w) : Subfunctor (pairPresheaf X) where
  obj _ := {p | p.1 = p.2}
  map f p same := show X.map f p.1 = X.map f p.2 from congrArg (fun x => X.map f x) same

theorem eq_of_mem_diagonal {X : Cᵒᵖ ⥤ Type w} {c : Cᵒᵖ} {a b : X.obj c}
    {p : X.obj c × X.obj c} (inDiagonal : p ∈ (diagonal X).obj c) (over : p = (a, b)) :
    a = b := by
  subst over
  exact inDiagonal

/-- **The identity structure of a presheaf at a stage**: points are the elements at
the stage, and a proof of `a = b` is an element of the diagonal over `(a, b)`. -/
def presheafIdentity (X : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ) : IdStructure.{w} where
  Pt := X.obj c
  Pf a b := {p : X.obj c × X.obj c // p ∈ (diagonal X).obj c ∧ p = (a, b)}
  refl a := ⟨(a, a), rfl, rfl⟩
  inv {a b} p := ⟨(b, a), (eq_of_mem_diagonal p.2.1 p.2.2).symm, rfl⟩
  comp {a _ d} p q := ⟨(a, d),
    (eq_of_mem_diagonal p.2.1 p.2.2).trans (eq_of_mem_diagonal q.2.1 q.2.2), rfl⟩

/-- **Presheaf identity is extensional**: all proofs of `a = b` are equal. -/
theorem presheafIdentity_sat_uip (X : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ) :
    (presheafIdentity X c).Sat .uip :=
  fun p q => Subtype.ext (p.2.2.trans q.2.2.symm)

theorem presheafIdentity_mem_hsetFragment (X : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ) :
    presheafIdentity X c ∈ hsetFragment := by
  have uip : (presheafIdentity X c).Sat .uip := presheafIdentity_sat_uip X c
  refine mem_hsetFragment_iff.mpr ?_
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact uip
  · exact fun _ _ _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _

variable (C)

/-- The identity structures of all presheaves on `C`, at all stages. -/
def presheafIdentities : Set IdStructure.{w} :=
  {M | ∃ (X : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ), M = presheafIdentity X c}

/-- **The presheaf universe of identities does not host the groupoid laws
faithfully**: it lies in the h-set fragment. -/
theorem not_hostsFaithfully_presheafIdentities :
    ¬ HostsFaithfully IdStructure.Sat (presheafIdentities C : Set IdStructure.{w}) groupoidLaws := by
  apply not_hostsFaithfully_of_subset_thin
  rintro _ ⟨X, c, rfl⟩
  exact (presheafIdentity_sat_uip X c : (presheafIdentity X c).Sat .uip)

end PresheafIdentity

/-! ## Presheaves of groupoids -/

section GroupoidPresheaves

open CategoryTheory

variable (C : Type) [Category.{0} C]

/-- The stage identities of presheaves of small groupoids on `C`. -/
def groupoidPresheafIdentities : Set IdStructure.{0} :=
  {M | ∃ (X : Cᵒᵖ ⥤ Grpd.{0, 0}) (c : Cᵒᵖ), M = ofGroupoid (X.obj c)}

theorem groupoidPresheafIdentities_subset_groupoidUniverse :
    groupoidPresheafIdentities C ⊆ groupoidUniverse.{0} := by
  rintro _ ⟨X, c, rfl⟩
  exact ofGroupoid_mem_groupoidUniverse (X.obj c)

/-- Constant presheaves contain every small groupoid. -/
theorem groupoidValued_subset_groupoidPresheafIdentities (c₀ : C) :
    groupoidValued ⊆ groupoidPresheafIdentities C := by
  rintro _ ⟨G, _, rfl⟩
  exact ⟨(Functor.const Cᵒᵖ).obj (Grpd.of G), Opposite.op c₀, rfl⟩

/-- **Presheaves of groupoids host the groupoid laws faithfully** over any category
with an object. -/
theorem hostsFaithfully_groupoidPresheaves (c₀ : C) :
    HostsFaithfully IdStructure.Sat (groupoidPresheafIdentities C) groupoidLaws :=
  hostsFaithfully_groupoidValued.mono (groupoidValued_subset_groupoidPresheafIdentities C c₀)

/-- A constant presheaf of groupoids with a non-trivial loop has a stage identity
outside the h-set fragment. -/
theorem constant_xor_not_mem_hsetFragment (c₀ : C) :
    ∃ M ∈ groupoidPresheafIdentities C, M ∉ hsetFragment.{0} :=
  ⟨xorGroupoidModel, groupoidValued_subset_groupoidPresheafIdentities C c₀ xorGroupoidModel_mem,
    fun member => xorGroupoidModel_not_uip (hsetFragment_subset_thin member)⟩

end GroupoidPresheaves

end IdentityProofs

end Mettapedia.Logic.TheoryModel
