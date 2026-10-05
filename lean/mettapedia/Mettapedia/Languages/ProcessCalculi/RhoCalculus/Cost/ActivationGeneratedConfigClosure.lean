import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedStackClosure

/-!
# The configuration readout and the generated normalizer

The clauses of the configuration readout, success of the readout as the configuration image,
and closure of configuration images under the generated normalizer: the image of the
normalized syntax has the same purses, while its code may change its quote and drop syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem config_zero_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported) (fuel : Nat) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:wrapped-constructor:PZero" [])).map Subtype.val =
      (code? fuel 0 (.apply "$cost:wrapped-constructor:PZero" [])).map Subtype.val := by
  simp only [config?_val, code?_val]; rfl

theorem config_drop_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:wrapped-constructor:PDrop" [source])).map Subtype.val =
      (code? fuel 0 (.apply "$cost:wrapped-constructor:PDrop" [source])).map Subtype.val := by
  simp only [config?_val, code?_val]; rfl

theorem config_collection_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (sources : List Pattern) :
    (config? location free supported (fuel + 1) (.collection .hashBag sources none)).map
      Subtype.val = (configList? location free supported fuel sources).map Subtype.val := by
  simp only [config?_val, configList?_val]; rfl

theorem configList_nil_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported) (fuel : Nat) :
    (configList? location free supported (fuel + 1) []).map Subtype.val = some .nil :=
  configList?_val _ _ _ _ _

theorem configList_cons_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) (sources : List Pattern) :
    (configList? location free supported (fuel + 1) (source :: sources)).map Subtype.val =
      (do
        let head ← (config? location free supported fuel source).map Subtype.val
        let tail ← (configList? location free supported fuel sources).map Subtype.val
        some (CostTerm.par head tail)) := by
  simp only [configList?_val, config?_val]; rfl

theorem config_parser_image {location : CostName LiteralAuthority}
    {free : location.purseInventory = 0} {supported : location.RuntimeSupported}
    {fuel : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
    (parsed : (config? location free supported fuel source).map Subtype.val = some term) :
    ConfigImage location source term :=
  readConfig_image ((config?_val location free supported fuel source).symm.trans parsed)

theorem ConfigImage.parser_eventually {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority} (image : ConfigImage location source term)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (config? location free supported fuel source).map Subtype.val = some term := by
  simpa only [config?_val] using image.read_eventually

theorem ConfigListImage.parser_eventually {location : CostName LiteralAuthority}
    {sources : List Pattern} {term : CostTerm LiteralAuthority}
    (image : ConfigListImage location sources term) (free : location.purseInventory = 0)
    (supported : location.RuntimeSupported) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (configList? location free supported fuel sources).map Subtype.val = some term := by
  simpa only [configList?_val] using image.read_eventually

mutual
  theorem ConfigImage.normalize_image {Measure : Type*} [AddCommMonoid Measure]
      {location : CostName LiteralAuthority} {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigImage location source term) (weight : CostStack LiteralAuthority → Measure) :
      ∃ normalized, ConfigImage location (normalizeReflective wrappedRhoDeclaration source) normalized ∧
        normalized.components.physicalPurseMeasure weight = term.components.physicalPurseMeasure weight := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | drop name =>
      obtain ⟨normalized, normalizedImage⟩ := (CodeImage.drop name).normalize_image
      refine ⟨normalized, normalizedImage.toConfigImage location, ?_⟩
      rw [normalizedImage.purseFree.components_physicalPurseMeasure_zero,
        (CodeImage.drop name).purseFree.components_physicalPurseMeasure_zero]
    | signed signature accepted process =>
      obtain ⟨normalized, normalizedImage⟩ := (CodeImage.signed signature accepted process).normalize_image
      refine ⟨normalized, normalizedImage.toConfigImage location, ?_⟩
      rw [normalizedImage.purseFree.components_physicalPurseMeasure_zero,
        (CodeImage.signed signature accepted process).purseFree.components_physicalPurseMeasure_zero]
    | @contact leftSource stackSource code stackValue left stack =>
      obtain ⟨normalized, normalizedImage, balance⟩ := left.normalize_image weight
      refine ⟨locatedContact location normalized stackValue, ?_, ?_⟩
      · change ConfigImage location (.apply "$cost:apparatus-constructor:contact"
          [normalizeReflective wrappedRhoDeclaration _, .apply "$cost:apparatus-constructor:funding"
            [normalizeReflective wrappedRhoDeclaration _]]) _
        rw [stack.normalize_identity]
        exact .contact normalizedImage stack
      · simp only [locatedContact, CostTerm.components, CostConfig.physicalPurseMeasure_add]
        rw [balance]
    | collection codes =>
      obtain ⟨normalized, normalizedImage, balance⟩ := codes.normalize_image weight
      exact ⟨normalized, .collection normalizedImage, balance⟩

  theorem ConfigListImage.normalize_image {Measure : Type*} [AddCommMonoid Measure]
      {location : CostName LiteralAuthority} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) (weight : CostStack LiteralAuthority → Measure) :
      ∃ normalized, ConfigListImage location (normalizeReflectiveList wrappedRhoDeclaration sources) normalized ∧
        normalized.components.physicalPurseMeasure weight = term.components.physicalPurseMeasure weight := by
    cases image with
    | nil => exact ⟨_, .nil, rfl⟩
    | cons head tail =>
      obtain ⟨normalizedHead, headImage, headBalance⟩ := head.normalize_image weight
      obtain ⟨normalizedTail, tailImage, tailBalance⟩ := tail.normalize_image weight
      refine ⟨.par normalizedHead normalizedTail, .cons headImage tailImage, ?_⟩
      simp only [CostTerm.components, CostConfig.physicalPurseMeasure_add]
      rw [headBalance, tailBalance]
end

theorem config_parser_normalization_closed {Measure : Type*} [AddCommMonoid Measure]
    {location : CostName LiteralAuthority} {free : location.purseInventory = 0}
    {supported : location.RuntimeSupported} {fuel : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority}
    (parsed : (config? location free supported fuel source).map Subtype.val = some term)
    (weight : CostStack LiteralAuthority → Measure) :
    ∃ normalized fuel,
      (config? location free supported fuel (normalizeReflective wrappedRhoDeclaration source)).map
        Subtype.val = some normalized ∧
      normalized.components.physicalPurseMeasure weight = term.components.physicalPurseMeasure weight := by
  obtain ⟨normalized, image, balance⟩ := (config_parser_image parsed).normalize_image weight
  obtain ⟨fuel, readback⟩ := image.parser_eventually free supported
  exact ⟨normalized, fuel, readback fuel (le_refl fuel), balance⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
