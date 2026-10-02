import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationNormalization

/-!
# Constructive old-parser readback of serialized admission

The reifier constructs actual existing decoder-image witnesses. Raw parallel
trees are presented by parser collections with their required trailing nils;
their exact normalized readout agrees with the original raw syntax. Fixed
funding locations remain explicit, and every stack preserves its ordered
accepted whole-signature atoms. No raw-key injectivity assumption is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

theorem RawCostTerm.normalized_components_keySorted (term : RawCostTerm) :
    KeySorted RawCostTerm.key term.normalize.components := by
  cases term with
  | par left right =>
      change KeySorted _ (RawCostTerm.fromComponents (stableKeySort RawCostTerm.key
        (left.normalize.components ++ right.normalize.components))).components
      rw [RawCostTerm.components_fromComponents]
      · exact stableKeySort_keySorted _ _
      · apply stableKeySort_forall
        exact List.forall_append.mpr ⟨RawCostTerm.components_forall_isComponent _,
          RawCostTerm.components_forall_isComponent _⟩
  | nil => simp [RawCostTerm.components, KeySorted]
  | signed process signature => simp [RawCostTerm.normalize, RawCostTerm.components, KeySorted]
  | drop name => simp [RawCostTerm.normalize, RawCostTerm.components, KeySorted]
  | purse location stack => simp [RawCostTerm.normalize, RawCostTerm.components, KeySorted]

theorem RawCostTerm.fromComponents_normalized_components (term : RawCostTerm) :
    RawCostTerm.fromComponents term.normalize.components = term.normalize := by
  cases term with
  | par left right =>
      change RawCostTerm.fromComponents (RawCostTerm.fromComponents (stableKeySort RawCostTerm.key
        (left.normalize.components ++ right.normalize.components))).components = _
      rw [RawCostTerm.components_fromComponents]
      apply stableKeySort_forall
      exact List.forall_append.mpr ⟨RawCostTerm.components_forall_isComponent _,
        RawCostTerm.components_forall_isComponent _⟩
  | nil => rfl
  | signed process signature => rfl
  | drop name => rfl
  | purse location stack => rfl

theorem RawCostTerm.normalize_par_nil (term : RawCostTerm) :
    (RawCostTerm.par term .nil).normalize = term.normalize := by
  change RawCostTerm.fromComponents (stableKeySort RawCostTerm.key (term.normalize.components ++ [])) = _
  rw [List.append_nil, stableKeySort_eq_self_of_keySorted _ term.normalized_components_keySorted,
    RawCostTerm.fromComponents_normalized_components]

theorem RawCostTerm.normalize_nil_par (term : RawCostTerm) :
    (RawCostTerm.par .nil term).normalize = term.normalize := by
  change RawCostTerm.fromComponents (stableKeySort RawCostTerm.key ([] ++ term.normalize.components)) = _
  rw [List.nil_append, stableKeySort_eq_self_of_keySorted _ term.normalized_components_keySorted,
    RawCostTerm.fromComponents_normalized_components]

namespace ActivationGenerated.SerializationAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  theorem NameAdmitted.readback :
      ∀ {depth : Nat} {name : RawCostName}, NameAdmitted depth name →
        ∃ source decoded, NameImage depth source decoded ∧
          name.normalize = (literalEncodeName decoded).normalize := by
    intro depth name image
    cases image with
    | bvar bound => exact ⟨_, .bvar _, .bvar bound, rfl⟩
    | quote code =>
        obtain ⟨source, decoded, codeImage, same⟩ := code.readback
        exact ⟨.apply "$cost:wrapped-constructor:NQuote" [source], .quote decoded,
          .quote codeImage, raw_quote_normalize_congr same⟩

  theorem CodeAdmitted.readback :
      ∀ {depth : Nat} {term : RawCostTerm}, CodeAdmitted depth term →
        ∃ source decoded, CodeImage depth source decoded ∧
          term.normalize = (literalEncodeTerm decoded).normalize := by
    intro depth term image
    cases image with
    | zero => exact ⟨_, .nil, .zero, rfl⟩
    | drop name =>
        obtain ⟨source, decoded, nameImage, same⟩ := name.readback
        refine ⟨.apply "$cost:wrapped-constructor:PDrop" [source], .drop decoded, .drop nameImage, ?_⟩
        change RawCostTerm.drop _ = RawCostTerm.drop _
        rw [same]
        rfl
    | signed process signature =>
        obtain ⟨core, decoded, processImage, same⟩ := process.readback
        cases signature with
        | @accepted source checked accepted =>
            refine ⟨.apply "$cost:apparatus-constructor:signed" [core, source], .signed decoded checked.val,
              .signed checked accepted processImage, ?_⟩
            have encoded : literalEncodeTerm (.signed decoded checked.val) =
                .signed (literalEncodeProc decoded) [literalAuthorityKey source] := by
              change RawCostTerm.signed _ (encodeCostSig (checked.val.map literalAuthorityKey)) = _
              rw [checked.property.1, literalEncodeSig_singleton]
              rfl
            rw [encoded]
            change RawCostTerm.signed _ _ = RawCostTerm.signed _ _
            rw [same]
    | @par _ left right first second =>
        obtain ⟨leftSource, leftTerm, leftImage, leftSame⟩ := first.readback
        obtain ⟨rightSource, rightTerm, rightImage, rightSame⟩ := second.readback
        refine ⟨.collection .hashBag [leftSource, rightSource] none,
          .par leftTerm (.par rightTerm .nil), .collection (.cons leftImage (.cons rightImage .nil)), ?_⟩
        change (RawCostTerm.par left right).normalize =
          (RawCostTerm.par (literalEncodeTerm leftTerm) (.par (literalEncodeTerm rightTerm) .nil)).normalize
        exact raw_term_par_normalize_congr leftSame
          (rightSame.trans (RawCostTerm.normalize_par_nil _).symm)

  theorem ProcAdmitted.readback :
      ∀ {depth : Nat} {process : RawCostProc}, ProcAdmitted depth process →
        ∃ source decoded, ProcImage depth source decoded ∧
          process.normalize = (literalEncodeProc decoded).normalize := by
    intro depth process image
    cases image with
    | zero => exact ⟨_, .nil, .zero, rfl⟩
    | send name code =>
        obtain ⟨channelSource, channel, nameImage, nameSame⟩ := name.readback
        obtain ⟨payloadSource, payload, codeImage, codeSame⟩ := code.readback
        refine ⟨.apply "$cost:base-constructor:POutput" [channelSource, payloadSource],
          .send channel payload, .send nameImage codeImage, ?_⟩
        change RawCostProc.send _ _ = RawCostProc.send _ _
        rw [nameSame, codeSame]
        rfl
    | recv name code =>
        obtain ⟨channelSource, channel, nameImage, nameSame⟩ := name.readback
        obtain ⟨bodySource, body, codeImage, codeSame⟩ := code.readback
        refine ⟨.apply "$cost:base-constructor:PInput" [channelSource, .lambda none bodySource],
          .recv channel body, .recv nameImage codeImage, ?_⟩
        change RawCostProc.recv _ _ = RawCostProc.recv _ _
        rw [nameSame, codeSame]
        rfl
    | par first second =>
        obtain ⟨leftSource, leftTerm, leftImage, leftSame⟩ := first.readback
        obtain ⟨rightSource, rightTerm, rightImage, rightSame⟩ := second.readback
        exact ⟨.collection .hashBag [leftSource, rightSource] none, .par leftTerm rightTerm,
          .pair leftImage rightImage, raw_proc_par_normalize_congr leftSame rightSame⟩
end

theorem ConfigAdmitted.readback {rawLocation : RawCostName} {term : RawCostTerm}
    (image : ConfigAdmitted rawLocation term) (location : CostName LiteralAuthority)
    (sameLocation : rawLocation.normalize = (literalEncodeName location).normalize) :
    ∃ source decoded, ConfigImage location source decoded ∧
      term.normalize = (literalEncodeTerm decoded).normalize := by
  induction image with
  | code body =>
      obtain ⟨source, decoded, codeImage, same⟩ := body.readback
      exact ⟨source, decoded, codeImage.toConfigImage location, same⟩
  | purse stack =>
      obtain ⟨source, decoded, stackImage, same⟩ := stack.readback
      refine ⟨.apply "$cost:apparatus-constructor:contact"
        [.apply "$cost:wrapped-constructor:PZero" [], .apply "$cost:apparatus-constructor:funding" [source]],
        locatedContact location .nil decoded, .contact .zero stackImage, ?_⟩
      change (RawCostTerm.purse rawLocation _).normalize =
        (RawCostTerm.par .nil (.purse (literalEncodeName location) (literalEncodeStack decoded))).normalize
      rw [RawCostTerm.normalize_nil_par]
      simp only [RawCostTerm.normalize, stack.normalize_identity, sameLocation, same]
  | @par left right first second leftIH rightIH =>
      obtain ⟨leftSource, leftTerm, leftImage, leftSame⟩ := leftIH
      obtain ⟨rightSource, rightTerm, rightImage, rightSame⟩ := rightIH
      refine ⟨.collection .hashBag [leftSource, rightSource] none,
        .par leftTerm (.par rightTerm .nil), .collection (.cons leftImage (.cons rightImage .nil)), ?_⟩
      change (RawCostTerm.par left right).normalize =
        (RawCostTerm.par (literalEncodeTerm leftTerm) (.par (literalEncodeTerm rightTerm) .nil)).normalize
      exact raw_term_par_normalize_congr leftSame
        (rightSame.trans (RawCostTerm.normalize_par_nil _).symm)

/-- Reification reads the actual old parser and preserves the complete raw
component multiset, including locations, literal seals and ordered stacks. -/
theorem configuration_parser_readback {channelSource : Pattern} {rawLocation : RawCostName}
    {location : CostName LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (sameLocation : rawLocation.normalize = (literalEncodeName location).normalize)
    (config : RawCostConfig) (images : config.Forall (ConfigAdmitted rawLocation))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term)) :
    ∃ source decoded fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel source).map
        Subtype.val = some decoded ∧
      ((literalEncodeTerm decoded).normalizeConfig : Multiset RawCostTerm) = (config : Multiset RawCostTerm) := by
  obtain ⟨source, decoded, image, same⟩ := (ConfigAdmitted.fromComponents images).readback location sameLocation
  obtain ⟨fuel, readback⟩ := image.parser_eventually channelImage.purseInventory_zero channelImage.runtimeSupported
  refine ⟨source, decoded, fuel, readback fuel (le_refl fuel), ?_⟩
  calc
    ((literalEncodeTerm decoded).normalizeConfig : Multiset RawCostTerm) =
        ((literalEncodeTerm decoded).normalize.components : Multiset RawCostTerm) := stableKeySort_toMultiset _ _
    _ = ((RawCostTerm.fromComponents config).normalize.components : Multiset RawCostTerm) :=
      congrArg (fun term : RawCostTerm => (term.components : Multiset RawCostTerm)) same.symm
    _ = (config : Multiset RawCostTerm) := RawCostTerm.normalize_fromComponents_toMultiset config components normalized

end ActivationGenerated.SerializationAdmission
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
