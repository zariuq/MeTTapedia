import Mettapedia.Languages.Agda.SourceMetatheory.PiInjectivity

/-! Audit every declaration whose actual origin is a promoted source module,
including private and generated declarations. The independent-source import
boundary is checked against the compiled transitive project closure. -/

open Lean Lean.Elab.Command
run_cmd do
  let modules := [`Mettapedia.Languages.Agda.SourceMetatheory.WeakHead, `Mettapedia.Languages.Agda.SourceMetatheory.WeakHeadTransport, `Mettapedia.Languages.Agda.SourceMetatheory.World, `Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropPacks, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropRelation, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropEscape, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropReflexivity, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropNeutral, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropPiParts, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropCoherence, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropLift, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.AnnotationBound, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TypedExpansion, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiApplication, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ConversionClauses, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticConversion, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TypeEqualityClosure, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TermEqualityClosure, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiApplicationEquality, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiIntroduction, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.RenamingClauses, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticRenaming, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticSubstitution, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.Validity, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropUniverses, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropDependentUniverse, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityBasic, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityEquality, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityPi, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityPiEquality, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiInstantiationEquality, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityApplication, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityLambda, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityComputation, `Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.Fundamental, `Mettapedia.Languages.Agda.SourceMetatheory.PiInjectivity]
  let allowed := [``propext, ``Quot.sound]
  let env ← getEnv
  for entry in env.header.modules do
    let name := entry.module.toString
    if name.startsWith "Mettapedia." &&
        !(name.startsWith "Mettapedia.Languages.Agda.StaticSpecification." ||
          name.startsWith "Mettapedia.Languages.Agda.StaticMetatheory." ||
          name.startsWith "Mettapedia.Languages.Agda.SourceEvidence." ||
          name.startsWith "Mettapedia.Languages.Agda.SourceMetatheory.") then
      throwError "Forbidden project import in source-only closure: {name}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) then
      if modules.contains origin.module then
        let axioms ← collectAxioms name
        let excess := axioms.filter fun dependency => !allowed.contains dependency
        unless excess.isEmpty do throwError "{name}: excess axioms {excess}"
        count := count + 1
        logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"Source metatheory promotion: {count} module-origin declarations within [propext, Quot.sound]."
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.fundamentalContext
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.fundamentalType
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.fundamentalTyping
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.fundamentalTypeEquality
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.fundamentalTermEquality
#print axioms Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.sourcePiInjectivity
