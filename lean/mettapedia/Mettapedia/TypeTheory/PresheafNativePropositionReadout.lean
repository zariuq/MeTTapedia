import Mettapedia.TypeTheory.PresheafNativePredicateRefinement

/-!
# Native proposition readouts and the fixed truth-proof family

Native propositions are ordinary contextual sieve values. Their natural
sections correspond to actual predicate subfunctors through characteristic
maps. The truth-proof family is fixed over the global sieve presheaf; its
fibres are subsingleton and contain proofs exactly at the maximal sieve.
No internal universe or proof-relevant witness reconstruction is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePropositionReadout

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafClassifier ContextualLocalUniverses NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

abbrev PropositionTerm (P : Cᵒᵖ ⥤ Type u) := (propositions P).sections

def sectionCharacteristic (term : PropositionTerm P) : P ⟶ omegaFunctor where
  app world := TypeCat.ofHom fun value => term.val ⟨world, value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (term.property (CategoryOfElements.homMk
      (F := P) ⟨first, value⟩ ⟨second, P.map arrow value⟩ arrow rfl)).symm

def characteristicSection (name : P ⟶ omegaFunctor (C := C)) : PropositionTerm P where
  val point := name.app point.1 point.2
  property := by
    intro first second arrow
    have natural := name.naturality_apply arrow.val first.2
    rw [arrow.property] at natural
    exact natural.symm

def sectionCharacteristicEquiv (P : Cᵒᵖ ⥤ Type u) :
    PropositionTerm P ≃ (P ⟶ omegaFunctor (C := C)) where
  toFun := sectionCharacteristic
  invFun := characteristicSection
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by ext world value; rfl

noncomputable def readoutEquiv (P : Cᵒᵖ ⥤ Type u) :
    PropositionTerm P ≃ Subfunctor P :=
  (sectionCharacteristicEquiv P).trans (natTransEquivSubfunctor P)

noncomputable def quote (predicate : Subfunctor P) : PropositionTerm P :=
  (readoutEquiv P).symm predicate

noncomputable def holds (term : PropositionTerm P) : Subfunctor P :=
  readoutEquiv P term

theorem holds_quote (predicate : Subfunctor P) : holds (quote predicate) = predicate :=
  (readoutEquiv P).apply_symm_apply predicate

theorem quote_holds (term : PropositionTerm P) : quote (holds term) = term :=
  (readoutEquiv P).symm_apply_apply term

theorem holds_member_iff (term : PropositionTerm P) (world : Cᵒᵖ) (value : P.obj world) :
    value ∈ (holds term).obj world ↔ term.val ⟨world, value⟩ = (⊤ : Sieve world.unop) :=
  Sieve.id_mem_iff_eq_top

noncomputable def characteristic (predicate : Subfunctor P) : P ⟶ omegaFunctor :=
  (natTransEquivSubfunctor P).symm predicate

theorem characteristic_quote (predicate : Subfunctor P) :
    sectionCharacteristic (quote predicate) = characteristic predicate := rfl

theorem characteristic_member_iff (predicate : Subfunctor P) (world : Cᵒᵖ)
    (value : P.obj world) :
    value ∈ predicate.obj world ↔ (characteristic predicate).app world value = (⊤ : Sieve world.unop) := by
  have readout := holds_member_iff (quote predicate) world value
  rw [holds_quote predicate] at readout
  exact readout

/-- Characteristic names commute with actual context substitution. -/
theorem characteristic_preimage (substitution : Q ⟶ P) (predicate : Subfunctor P) :
    characteristic (predicate.preimage substitution) = substitution ≫ characteristic predicate := by
  apply (natTransEquivSubfunctor Q).injective
  rw [characteristic, Equiv.apply_symm_apply]
  ext world value
  change substitution.app world value ∈ predicate.obj world ↔
    ((characteristic predicate).app world (substitution.app world value)).arrows (𝟙 world.unop)
  exact (characteristic_member_iff predicate world (substitution.app world value)).trans
    Sieve.id_mem_iff_eq_top.symm

/-- Actual proofs of truth form a fixed family over the global sieve
presheaf. Only this proposition-valued evidence is subsingleton. -/
def truthFamily : DisplayedFamily (omegaFunctor (C := C)) where
  obj point := ULift.{u} (PLift (point.2 = (⊤ : Sieve point.1.unop)))
  map arrow := TypeCat.ofHom fun proof => ⟨⟨by
    have transported := congrArg (fun sieve => omegaFunctor.map arrow.val sieve) proof.down.down
    exact arrow.property.symm.trans
      (transported.trans (sievePullback_top arrow.val.unop))⟩⟩
  map_id _ := by apply ConcreteCategory.hom_ext; intro proof; apply Subsingleton.elim
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro proof; apply Subsingleton.elim

instance truthFamily_subsingleton (point : (omegaFunctor (C := C)).Elements) :
    Subsingleton (truthFamily.obj point) := inferInstanceAs
  (Subsingleton (ULift.{u} (PLift (point.2 = (⊤ : Sieve point.1.unop)))))

noncomputable def guard (predicate : Subfunctor P) : NativeType P :=
  ⟨omegaFunctor, truthFamily, characteristic predicate⟩

/-- The guard's parameters and family remain fixed; only the actual
predicate characteristic name is substituted. -/
theorem guard_reindex (substitution : Q ⟶ P) (predicate : Subfunctor P) :
    (guard predicate).reindex substitution = guard (predicate.preimage substitution) := by
  exact congrArg (fun name => (⟨omegaFunctor, truthFamily, name⟩ : NativeType Q))
    (characteristic_preimage substitution predicate).symm

/-- The ordinary proposition type has a fixed parameter context and
family. It is not an internal universe of native family presentations. -/
def nativeOmega (P : Cᵒᵖ ⥤ Type u) : NativeType P :=
  ⟨terminalFace C, propositions (terminalFace C),
    (presheafCwfWithTerminal C).toEmpty P⟩

theorem nativeOmega_decode (P : Cᵒᵖ ⥤ Type u) :
    (nativeOmega P).decoded = propositions P := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  rfl

theorem nativeOmega_reindex (substitution : Q ⟶ P) :
    (nativeOmega P).reindex substitution = nativeOmega Q := by
  apply congrArg (fun name => (⟨terminalFace C,
    propositions (terminalFace C), name⟩ : NativeType Q))
  exact (presheafCwfWithTerminal C).toEmpty_unique Q
    (substitution ≫ (presheafCwfWithTerminal C).toEmpty P)

def nativeTermEquiv (P : Cᵒᵖ ⥤ Type u) :
    (nativeOmega P).decoded.sections ≃ PropositionTerm P :=
  Equiv.cast (congrArg (fun family : DisplayedFamily P => ↥family.sections) (nativeOmega_decode P))

noncomputable def nativeQuote (predicate : Subfunctor P) :
    (nativeOmega P).decoded.sections := (nativeTermEquiv P).symm (quote predicate)

noncomputable def nativeHolds (term : (nativeOmega P).decoded.sections) : Subfunctor P :=
  holds (nativeTermEquiv P term)

theorem nativeHolds_nativeQuote (predicate : Subfunctor P) :
    nativeHolds (nativeQuote predicate) = predicate := by
  unfold nativeHolds nativeQuote
  rw [Equiv.apply_symm_apply, holds_quote]

theorem nativeQuote_nativeHolds (term : (nativeOmega P).decoded.sections) :
    nativeQuote (nativeHolds term) = term := by
  unfold nativeHolds nativeQuote
  rw [quote_holds, Equiv.symm_apply_apply]

def substituteProposition (substitution : Q ⟶ P) (term : PropositionTerm P) :
    PropositionTerm Q :=
  characteristicSection (substitution ≫ sectionCharacteristic term)

theorem substituteProposition_value (substitution : Q ⟶ P)
    (term : PropositionTerm P) (world : Cᵒᵖ) (value : Q.obj world) :
    (substituteProposition substitution term).val ⟨world, value⟩ =
      term.val ⟨world, substitution.app world value⟩ := rfl

theorem substituteProposition_quote (substitution : Q ⟶ P) (predicate : Subfunctor P) :
    substituteProposition substitution (quote predicate) =
      quote (predicate.preimage substitution) := by
  apply (sectionCharacteristicEquiv Q).injective
  change substitution ≫ characteristic predicate = characteristic (predicate.preimage substitution)
  exact (characteristic_preimage substitution predicate).symm

theorem holds_substituteProposition (substitution : Q ⟶ P) (term : PropositionTerm P) :
    holds (substituteProposition substitution term) = (holds term).preimage substitution := by
  conv_lhs => rw [← quote_holds term]
  rw [substituteProposition_quote, holds_quote]

end Mettapedia.TypeTheory.PresheafNativePropositionReadout
