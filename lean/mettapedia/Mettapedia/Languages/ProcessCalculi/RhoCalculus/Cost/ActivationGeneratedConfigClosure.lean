import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedStackClosure

/-!
# Configuration image and normalization closure

The existing parser's nested contacts and parallel collections form this
structural image. Normalization keeps the decoder domain and all physical
authority stacks; code readout may change its quote/drop syntax.
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
  cases parsed : code? fuel 0 (.apply "$cost:wrapped-constructor:PZero" []) <;>
    simp [config?, parsed]

theorem config_drop_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:wrapped-constructor:PDrop" [source])).map Subtype.val =
      (code? fuel 0 (.apply "$cost:wrapped-constructor:PDrop" [source])).map Subtype.val := by
  cases parsed : code? fuel 0 (.apply "$cost:wrapped-constructor:PDrop" [source]) <;>
    simp [config?, parsed]

theorem config_collection_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (sources : List Pattern) :
    (config? location free supported (fuel + 1) (.collection .hashBag sources none)).map
      Subtype.val = (configList? location free supported fuel sources).map Subtype.val := rfl

theorem configList_nil_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported) (fuel : Nat) :
    (configList? location free supported (fuel + 1) []).map Subtype.val = some .nil := rfl

theorem configList_cons_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) (sources : List Pattern) :
    (configList? location free supported (fuel + 1) (source :: sources)).map Subtype.val =
      (do
        let head ← (config? location free supported fuel source).map Subtype.val
        let tail ← (configList? location free supported fuel sources).map Subtype.val
        some (CostTerm.par head tail)) := by
  cases headParsed : config? location free supported fuel source <;>
    cases tailParsed : configList? location free supported fuel sources <;>
    simp [configList?, headParsed, tailParsed]

mutual
  inductive ConfigImage (location : CostName LiteralAuthority) :
      Pattern → CostTerm LiteralAuthority → Prop where
    | zero : ConfigImage location (.apply "$cost:wrapped-constructor:PZero" []) .nil
    | drop {source name} (image : NameImage 0 source name) :
        ConfigImage location (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name)
    | signed {source authority process} (signature : TypedSignature authority)
        (accepted : signature? authority = some signature) (image : ProcImage 0 source process) :
        ConfigImage location (.apply "$cost:apparatus-constructor:signed" [source, authority])
          (.signed process signature.val)
    | contact {left stackSource code stack}
        (leftImage : ConfigImage location left code) (stackImage : StackImage stackSource stack) :
        ConfigImage location (.apply "$cost:apparatus-constructor:contact"
          [left, .apply "$cost:apparatus-constructor:funding" [stackSource]])
          (locatedContact location code stack)
    | collection {sources term} (image : ConfigListImage location sources term) :
        ConfigImage location (.collection .hashBag sources none) term

  inductive ConfigListImage (location : CostName LiteralAuthority) :
      List Pattern → CostTerm LiteralAuthority → Prop where
    | nil : ConfigListImage location [] .nil
    | cons {source sources head tail} (headImage : ConfigImage location source head)
        (tailImage : ConfigListImage location sources tail) :
        ConfigListImage location (source :: sources) (.par head tail)
end

mutual
  theorem CodeImage.toConfigImage {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage 0 source term) (location : CostName LiteralAuthority) :
      ConfigImage location source term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop name
    | signed signature accepted process => exact .signed signature accepted process
    | collection codes => exact .collection (codes.toConfigListImage location)

  theorem CodeListImage.toConfigListImage {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeListImage 0 sources term) (location : CostName LiteralAuthority) :
      ConfigListImage location sources term := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .cons (head.toConfigImage location) (tail.toConfigListImage location)
end

private theorem config_parser_images (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported) :
    (∀ fuel source term, (config? location free supported fuel source).map Subtype.val = some term →
      ConfigImage location source term) ∧
    (∀ fuel sources term,
      (configList? location free supported fuel sources).map Subtype.val = some term →
        ConfigListImage location sources term) := by
  apply config?.mutual_induct
    (motive_1 := fun fuel source => ∀ term,
      (config? location free supported fuel source).map Subtype.val = some term →
        ConfigImage location source term)
    (motive_2 := fun fuel sources => ∀ term,
      (configList? location free supported fuel sources).map Subtype.val = some term →
        ConfigListImage location sources term)
  · intro source term parsed
    simp [config?] at parsed
  · intro fuel left stackSource leftIH term parsed
    cases leftParsed : config? location free supported fuel left with
    | none => simp [config?, leftParsed] at parsed
    | some code =>
      cases stackParsed : stack? fuel stackSource with
      | none => simp [config?, leftParsed, stackParsed] at parsed
      | some stack =>
        simp only [config?, leftParsed, stackParsed] at parsed
        change some (locatedContact location code.val stack.val) = some term at parsed
        cases parsed
        exact .contact (leftIH code.val (by rw [leftParsed]; rfl))
          (stack_parser_image (by rw [stackParsed]; rfl))
  · intro fuel sources listIH term parsed
    exact .collection (listIH term parsed)
  · intro fuel source notContact notCollection term parsed
    rw [config?.eq_4 location free supported source fuel notContact notCollection] at parsed
    cases codeParsed : code? fuel 0 source with
    | none => simp [codeParsed] at parsed
    | some code =>
      simp only [codeParsed] at parsed
      change some code.val = some term at parsed
      cases parsed
      exact (code_parser_image (by rw [codeParsed]; rfl)).toConfigImage location
  · intro sources term parsed
    simp [configList?] at parsed
  · intro fuel term parsed
    change some CostTerm.nil = some term at parsed
    cases parsed
    exact .nil
  · intro fuel source sources headIH tailIH term parsed
    cases headParsed : config? location free supported fuel source with
    | none => simp [configList?, headParsed] at parsed
    | some head =>
      cases tailParsed : configList? location free supported fuel sources with
      | none => simp [configList?, headParsed, tailParsed] at parsed
      | some tail =>
        simp only [configList?, headParsed, tailParsed] at parsed
        change some (CostTerm.par head.val tail.val) = some term at parsed
        cases parsed
        exact .cons (headIH head.val (by rw [headParsed]; rfl))
          (tailIH tail.val (by rw [tailParsed]; rfl))

theorem config_parser_image {location : CostName LiteralAuthority}
    {free : location.purseInventory = 0} {supported : location.RuntimeSupported}
    {fuel : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
    (parsed : (config? location free supported fuel source).map Subtype.val = some term) :
    ConfigImage location source term :=
  (config_parser_images location free supported).1 fuel source term parsed

mutual
  theorem ConfigImage.parser_eventually {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority} (image : ConfigImage location source term)
      (free : location.purseInventory = 0) (supported : location.RuntimeSupported) :
      ∃ bound, ∀ fuel, bound ≤ fuel →
        (config? location free supported fuel source).map Subtype.val = some term := by
    cases image with
    | zero =>
      refine ⟨2, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [config_zero_readout]
        cases fuel with
        | zero => omega
        | succ fuel => exact code_zero_readout fuel 0
    | drop name =>
      obtain ⟨bound, readback⟩ := (CodeImage.drop name).parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rw [config_drop_readout, readback fuel (by omega)]
    | signed signature accepted process =>
      obtain ⟨bound, readback⟩ := (CodeImage.signed signature accepted process).parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rw [config_signed_readout, readback fuel (by omega)]
    | contact left stack =>
      obtain ⟨leftBound, leftReadback⟩ := left.parser_eventually free supported
      obtain ⟨stackBound, stackReadback⟩ := stack.parser_eventually
      refine ⟨max leftBound stackBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [config_contact_readout, leftReadback fuel (by omega), stackReadback fuel (by omega)]
        rfl
    | collection codes =>
      obtain ⟨bound, readback⟩ := codes.parser_eventually free supported
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rw [config_collection_readout, readback fuel (by omega)]

  theorem ConfigListImage.parser_eventually {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) (free : location.purseInventory = 0)
      (supported : location.RuntimeSupported) :
      ∃ bound, ∀ fuel, bound ≤ fuel →
        (configList? location free supported fuel sources).map Subtype.val = some term := by
    cases image with
    | nil =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact configList_nil_readout location free supported fuel
    | cons head tail =>
      obtain ⟨headBound, headReadback⟩ := head.parser_eventually free supported
      obtain ⟨tailBound, tailReadback⟩ := tail.parser_eventually free supported
      refine ⟨max headBound tailBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [configList_cons_readout, headReadback fuel (by omega), tailReadback fuel (by omega)]
        rfl
end

theorem CodeImage.purseFree {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) : term.PurseFree := by
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp (readback fuel (le_refl fuel))
  subst term
  exact decoded.property.1

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
