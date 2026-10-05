import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassification

/-!
# Infinite material fibre and receipt controls

At stage n an actual material set contains n+1 distinct labelled cyclic
payloads. Its member restriction preserves each old material value. Small
receipt enumeration contains duplicate Boolean provenance for each member;
the saturated fibre codes retain the member and erase that provenance.

Every future fibre has authored enumeration data. New members appear at
every successor stage, so transport of a current enumeration alone cannot
provide the complete later fibre.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassificationControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualGeneratedUniverse ContextualMaterialSmallMapClassification
open PowerClassPresheafDescent.Controls (Stages world stageIndex growthLe)

def base : Stagesᵒᵖ ⥤ Type := ContextualWitnessCover.terminal

def context : LabelledContext Stages where
  base := base
  labels := {
    graph point := OutcomeLabels.chainGraph (stageIndex point.1)
    injective := by
      rintro ⟨first, firstValue⟩ ⟨second, secondValue⟩ same
      dsimp only at same
      rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
      have numbers := OutcomeLabels.chainValue_injective same
      have worlds : first = second := congrArg world numbers
      cases worlds
      cases firstValue
      cases secondValue
      rfl }

def point (level : Nat) : context.base.Elements := ⟨world level, PUnit.unit⟩

def advance (level : Nat) : point level ⟶ point (level + 1) :=
  CategoryOfElements.homMk (F := context.base) (point level) (point (level + 1))
    (homOfLE (Nat.le_succ level)).op.op rfl

def payloadGraph (number : Nat) : AccessiblePointedGraph :=
  AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph number) HSet.loop

def payload (number : Nat) : HSet := HSet.mk (payloadGraph number)

theorem payload_value (number : Nat) :
    payload number = HSet.kpair (OutcomeLabels.chainValue number) HSet.quineAtom := by
  rw [payload, payloadGraph, AccessiblePointedGraph.mk_kpairGraph,
    OutcomeLabels.mk_chainGraph, HSet.mk_loop]

theorem payload_injective : Function.Injective payload := by
  intro first second same
  rw [payload_value, payload_value] at same
  exact OutcomeLabels.chainValue_injective (HSet.kpair_inj.mp same).1

def carrier (position : context.base.Elements) : HSet :=
  HSet.range (fun index : Fin (stageIndex position.1 + 1) => payloadGraph index.val)

theorem mem_carrier (position : context.base.Elements) (value : HSet) :
    value ∈ carrier position ↔ ∃ index : Fin (stageIndex position.1 + 1), payload index.val = value :=
  HSet.mem_range

theorem carrier_monotone {first second : context.base.Elements} (step : first ⟶ second)
    {value : HSet} (member : value ∈ carrier first) : value ∈ carrier second := by
  obtain ⟨index, same⟩ := (mem_carrier first value).mp member
  exact (mem_carrier second value).mpr
    ⟨index.castLE (Nat.succ_le_succ (growthLe step.1)), same⟩

def domain : BareContextualFamilies.Family.{0, 0} context where
  carrier := carrier
  restrict step member := ⟨member.val, carrier_monotone step member.property⟩
  restrict_id _ _ := Subtype.ext rfl
  restrict_comp _ _ _ := Subtype.ext rfl

def member (position : context.base.Elements) (index : Fin (stageIndex position.1 + 1)) :
    domain.source.obj position :=
  ⟨payload index.val, (mem_carrier position _).mpr ⟨index, rfl⟩⟩

abbrev parameters : context.base.Elements ⥤ Type := {
  obj _ := PUnit.{1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl }

def parameterPoint (position : context.base.Elements) : parameters.Elements :=
  Functor.elementsMk parameters position PUnit.unit

def operation : NaturalHom domain.source parameters where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def change : NaturalHom parameters parameters := CoveredFuturePowerFunctor.identityHom parameters

def enumeration (position : context.base.Elements) (parameter : parameters.obj position) :
    Enumeration.{0, 1} (Fibre operation position (change.app position parameter)) where
  Carrier := Fin (stageIndex position.1 + 1) × Bool
  value receipt := ⟨member position receipt.1, Subsingleton.elim (α := PUnit.{1}) _ _⟩
  covered argument := by
    obtain ⟨index, same⟩ := (mem_carrier position argument.val.val).mp argument.val.property
    exact ⟨(index, false), Subtype.ext (Subtype.ext same)⟩

def futureData (position : context.base.Elements) (parameter : parameters.obj position) :
    ContextualEnumerationCovers.FutureEnumerations operation position parameter :=
  fun future => enumeration future.1 (parameters.map future.2 parameter)

theorem future_covered (position : context.base.Elements) (parameter : parameters.obj position) :
    Nonempty (ContextualEnumerationCovers.FutureEnumerations operation position parameter) :=
  ⟨futureData position parameter⟩

abbrev small := smallFamily domain operation change enumeration

def zeroCode (position : context.base.Elements) :
    small.obj (parameterPoint position) :=
  (fibreDecoder domain operation change enumeration (parameterPoint position)).symm
    ⟨member position ⟨0, Nat.zero_lt_succ _⟩, rfl⟩

theorem zeroCode_decode (position : context.base.Elements) :
    fibreDecoder domain operation change enumeration (parameterPoint position) (zeroCode position) =
      ⟨member position ⟨0, Nat.zero_lt_succ _⟩, rfl⟩ :=
  (fibreDecoder domain operation change enumeration (parameterPoint position)).apply_symm_apply _

def representedSection : (representedTotal domain operation change enumeration).sections :=
  ⟨fun position => ⟨PUnit.unit, zeroCode position⟩, by
    intro first second step
    apply congrArg (fun code =>
      (⟨PUnit.unit, code⟩ : (representedTotal domain operation change enumeration).obj second))
    change smallMap domain operation change enumeration
      (CategoryOfElements.homMk (F := parameters) (parameterPoint first)
        (parameterPoint second) step rfl) (zeroCode first) = zeroCode second
    apply (fibreDecoder domain operation change enumeration (parameterPoint second)).injective
    have raw := CategoryOfElements.homMk (F := parameters)
      (parameterPoint first) (parameterPoint second) step rfl
    refine (smallMap_decode domain operation change enumeration raw (zeroCode first)).trans ?_
    refine (congrArg (fibreRestriction domain operation change raw) (zeroCode_decode first)).trans ?_
    exact (Subtype.ext (Subtype.ext rfl)).trans (zeroCode_decode second).symm⟩

def materialSection := representedSectionEquiv domain operation change enumeration representedSection

theorem whole_section_inverse :
    (representedSectionEquiv domain operation change enumeration).symm materialSection = representedSection :=
  (representedSectionEquiv domain operation change enumeration).symm_apply_apply representedSection

theorem material_section_value (position : context.base.Elements) :
    (materialSection.val position).val.1.val = payload 0 := by
  exact congrArg (fun receipt => receipt.val.val)
    ((fibreDecoder domain operation change enumeration (parameterPoint position)).apply_symm_apply
      ⟨member position ⟨0, Nat.zero_lt_succ _⟩, rfl⟩)

def duplicateCode (position : context.base.Elements) (tag : Bool) :
    MaterialEnumerationDecoders.FibreCode (operation.app position) PUnit.unit
      (enumeration position PUnit.unit) :=
  MaterialEnumerationDecoders.receiptCode
    (MaterialEnumerationDecoders.fibreEnumeration (operation.app position) PUnit.unit
      (enumeration position PUnit.unit)) (⟨0, Nat.zero_lt_succ _⟩, tag)

theorem duplicate_codes_equal (position : context.base.Elements) :
    duplicateCode position true = duplicateCode position false :=
  (MaterialEnumerationDecoders.receiptCode_eq_iff _ _ _).mpr rfl

theorem raw_tag_has_no_code_readout (position : context.base.Elements) :
    ¬ ∃ readout : MaterialEnumerationDecoders.FibreCode (operation.app position) PUnit.unit
      (enumeration position PUnit.unit) → Bool,
      ∀ tag, readout (duplicateCode position tag) = tag := by
  rintro ⟨readout, reads⟩
  have impossible := (reads true).symm.trans
    ((congrArg readout (duplicate_codes_equal position)).trans (reads false))
  cases impossible

theorem new_payload_absent_before (level : Nat) :
    payload (level + 1) ∉ carrier (point level) := by
  intro belongs
  obtain ⟨index, same⟩ := (mem_carrier (point level) _).mp belongs
  have impossible := payload_injective same
  exact Nat.ne_of_lt index.isLt impossible

def newMember (level : Nat) : domain.source.obj (point (level + 1)) :=
  member (point (level + 1)) ⟨level + 1, Nat.lt_succ_self _⟩

theorem new_member_not_restricted (level : Nat) :
    ¬ ∃ old : domain.source.obj (point level), domain.source.map (advance level) old = newMember level := by
  rintro ⟨old, same⟩
  have value : old.val = payload (level + 1) := congrArg Subtype.val same
  exact new_payload_absent_before level (value ▸ old.property)

theorem carriers_vary_at_every_stage (level : Nat) :
    carrier (point level) ≠ carrier (point (level + 1)) := by
  intro same
  exact new_payload_absent_before level (same.symm ▸ (newMember level).property)

def newCode (level : Nat) : small.obj (parameterPoint (point (level + 1))) :=
  (fibreDecoder domain operation change enumeration (parameterPoint (point (level + 1)))).symm
    ⟨newMember level, rfl⟩

theorem newCode_decode (level : Nat) :
    fibreDecoder domain operation change enumeration (parameterPoint (point (level + 1))) (newCode level) =
      ⟨newMember level, rfl⟩ :=
  (fibreDecoder domain operation change enumeration (parameterPoint (point (level + 1)))).apply_symm_apply _

def smallAdvance (level : Nat) :
    ((parameterPoint (point level)) : parameters.Elements) ⟶
      ((parameterPoint (point (level + 1))) : parameters.Elements) :=
  CategoryOfElements.homMk (F := parameters) _ _ (advance level) rfl

theorem new_code_not_transported (level : Nat) :
    ¬ ∃ old : small.obj (parameterPoint (point level)), small.map (smallAdvance level) old = newCode level := by
  rintro ⟨old, same⟩
  apply new_member_not_restricted level
  refine ⟨(fibreDecoder domain operation change enumeration (parameterPoint (point level)) old).val, ?_⟩
  have decoded := congrArg
    (fibreDecoder domain operation change enumeration (parameterPoint (point (level + 1)))) same
  have restriction := decode_restriction domain operation change enumeration (smallAdvance level) old
  exact restriction.symm.trans
    ((congrArg Subtype.val decoded).trans (congrArg Subtype.val (newCode_decode level)))

theorem current_receipts_miss_new_payload (level : Nat)
    (receipt : (enumeration (point level) PUnit.unit).Carrier) :
    (domain.source.map (advance level) ((enumeration (point level) PUnit.unit).value receipt).val).val ≠
      payload (level + 1) := by
  intro same
  exact new_payload_absent_before level
    (same ▸ ((enumeration (point level) PUnit.unit).value receipt).val.property)

theorem future_receipt_reaches_new_payload (level : Nat) :
    ∃ receipt : (enumeration (point (level + 1)) PUnit.unit).Carrier,
      ((enumeration (point (level + 1)) PUnit.unit).value receipt).val = newMember level :=
  ⟨(⟨level + 1, Nat.lt_succ_self _⟩, false), rfl⟩

theorem cyclic_payload_is_retained (position : context.base.Elements) :
    HSet.snd ((materialSection.val position).val.1.val) = HSet.quineAtom := by
  rw [material_section_value, payload_value]
  exact HSet.snd_kpair _ _

/-! ## A complete natural section through both actual classification pullbacks -/

def fromInitial (position : context.base.Elements) : point 0 ⟶ position :=
  CategoryOfElements.homMk (F := context.base) (point 0) position
    (homOfLE (Nat.zero_le (stageIndex position.1))).op.op
    (Subsingleton.elim (α := PUnit.{1}) _ _)

def initialGenerator : ContextualEnumerationCovers.FutureGenerator operation :=
  ⟨point 0, PUnit.unit, futureData (point 0) PUnit.unit⟩

def futureReceipt (position : context.base.Elements) : (futureParameters domain operation).obj position :=
  ⟨initialGenerator, fromInitial position⟩

theorem futureReceipt_natural {first second : context.base.Elements} (step : first ⟶ second) :
    (futureParameters domain operation).map step (futureReceipt first) = futureReceipt second :=
  congrArg (Sigma.mk initialGenerator) (Subtype.ext (Subsingleton.elim _ _))

def futurePairSection : (pullback operation (futureChange domain operation)).sections :=
  ⟨fun position => ⟨(member position ⟨0, Nat.zero_lt_succ _⟩, futureReceipt position), rfl⟩, by
    intro first second step
    exact Subtype.ext (Prod.ext (Subtype.ext rfl) (futureReceipt_natural step))⟩

def futureRepresentedSection : (futureRepresented domain operation).sections :=
  (representedSectionEquiv domain operation (futureChange domain operation)
    (futureEnumerations domain operation)).symm futurePairSection

def universalFutureSection : (universalPullback domain operation).sections :=
  universalSectionEquiv domain operation futureRepresentedSection

theorem universal_future_whole_inverse :
    (universalSectionEquiv domain operation).symm universalFutureSection = futureRepresentedSection :=
  (universalSectionEquiv domain operation).symm_apply_apply futureRepresentedSection

theorem both_pullbacks_whole_section_inverse :
    representedSectionEquiv domain operation (futureChange domain operation)
      (futureEnumerations domain operation)
      ((universalSectionEquiv domain operation).symm universalFutureSection) = futurePairSection := by
  rw [universal_future_whole_inverse]
  exact (representedSectionEquiv domain operation (futureChange domain operation)
    (futureEnumerations domain operation)).apply_symm_apply futurePairSection

theorem recovered_cyclic_material_value (position : context.base.Elements) :
    ((futureTop domain operation).app position
      (((universalSectionEquiv domain operation).symm universalFutureSection).val position)).val = payload 0 := by
  have inverse := congrArg (fun term : (pullback operation (futureChange domain operation)).sections =>
    (term.val position).val.1.val) both_pullbacks_whole_section_inverse
  exact inverse

theorem concrete_parameter_cover (position : context.base.Elements) :
    Function.Surjective ((futureChange domain operation).app position) :=
  future_parameters_cover domain operation future_covered position

theorem concrete_source_cover (position : context.base.Elements) :
    Function.Surjective ((futureTop domain operation).app position) :=
  future_top_cover domain operation future_covered position

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassificationControls
