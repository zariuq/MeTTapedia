import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAtomLaws

/-! Attribute and relation declarations print and read with their original
names, primitive types and column order. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open ProgramProjection

theorem attribute_type_read (kind : AttributeType) (source : Pattern)
    (built : attributeType? kind = .ok source) :
    Reference.attributeType? source = some (IRCodec.attributeType kind) := by
  cases kind <;> cases built <;> rfl

theorem attribute_type_normalize (kind : AttributeType) :
    Frontend.normalize? (IRCodec.attributeType kind) = some (IRCodec.attributeType kind) := by
  cases kind <;> rfl

theorem attribute_read (column : Attribute) (source : Pattern)
    (built : attribute? column = .ok source) :
    (Reference.attribute? source).bind Frontend.normalize? = some (IRCodec.attributeData column) := by
  cases nameRead : identifier? column.name with
  | error reason => simp only [attribute?, nameRead] at built; cases built
  | ok name =>
      cases typeRead : attributeType? column.type with
      | error reason => simp only [attribute?, nameRead, typeRead] at built; cases built
      | ok kind =>
          simp only [attribute?, nameRead, typeRead] at built
          have same : node "attr" [name,empty,space,kind] = source := Except.ok.inj built
          subst source
          have projected := attribute_type_read _ _ typeRead
          change ((Reference.attributeType? kind).map fun kind => Pattern.apply "Attribute" [name,kind]).bind
            Frontend.normalize? = _
          rw [projected]
          change ((Frontend.sourceText? name).bind fun name =>
            (Frontend.normalize? (IRCodec.attributeType column.type)).bind fun kind =>
              some (Pattern.apply "Attribute" [IRCodec.atom name,kind])) = _
          rw [identifier_source_text _ _ nameRead, attribute_type_normalize]
          rfl

theorem attributes_read (values : List Attribute) (sources : List Pattern)
    (built : values.mapM attribute? = .ok sources) :
    (Reference.attributes? (separated "attributes-empty" "attributes-one" "attributes-more" sources)).bind
      Frontend.normalizeChildren? = some (values.map IRCodec.attributeData) := by
  apply separated_normalize _ _ _ _ Reference.attribute? _ attribute? IRCodec.attributeData attribute_read values sources built
  intro items
  exact separated_read _ _ _ _ _ rfl (fun _ => rfl) (fun _ _ => rfl) items

theorem declaration_read (declaration : RelationDeclaration) (source : Pattern)
    (built : declaration? declaration = .ok source) :
    ∃ code, Reference.itemInto? (node "item-declaration" [source]) [] = some [code] ∧
      Frontend.normalize? code = some (IRCodec.statement (.declaration declaration)) := by
  cases names : declaration.name with
  | nil => simp [declaration?, names] at built
  | cons name rest =>
      cases rest with
      | cons _ _ => simp [declaration?, names] at built
      | nil =>
          cases nameRead : identifier? name with
          | error reason => simp only [declaration?, names, nameRead] at built; cases built
          | ok identifier =>
              cases attrsRead : declaration.attributes.mapM attribute? with
              | error reason => simp only [declaration?, names, nameRead, attrsRead] at built; cases built
              | ok attributes =>
                  simp only [declaration?, names, nameRead, attrsRead] at built
                  have same : node "declaration" [directiveSpace,node "relations-one" [identifier],empty,empty,
                      separated "attributes-empty" "attributes-one" "attributes-more" attributes] = source := Except.ok.inj built
                  subst source
                  have normalized := attributes_read _ _ attrsRead
                  cases projected : Reference.attributes? (separated "attributes-empty" "attributes-one" "attributes-more" attributes) with
                  | none => simp [projected] at normalized
                  | some columns =>
                      simp only [projected, Option.bind_some] at normalized
                      refine ⟨Reference.declaration identifier columns, ?_, ?_⟩
                      · change ((Reference.attributes? (separated "attributes-empty" "attributes-one" "attributes-more" attributes)).bind
                          fun columns => Reference.relationsInto? (node "relations-one" [identifier]) columns []) = _
                        rw [projected]
                        rfl
                      · have nameNormalized : Frontend.normalize? (Reference.relation (node "qualified-name-one" [identifier])) =
                            some (IRCodec.relation declaration.name) := by
                          rw [names]
                          apply relation_normalize
                          simp [qualifiedName?, nameRead]
                        have declarationNormalized : Frontend.normalize? (.apply "RelationDeclaration"
                            [Reference.relation (node "qualified-name-one" [identifier]),Reference.vector columns]) =
                            some (IRCodec.declaration declaration) := by
                          apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
                          simp only [Frontend.normalizeChildren?, nameNormalized, normalize_vector _ _ normalized,
                            Option.bind_eq_bind, Option.bind_some]
                          rfl
                        change Frontend.normalize? (.apply "Declaration" [.apply "RelationDeclaration"
                          [Reference.relation (node "qualified-name-one" [identifier]),Reference.vector columns]]) = _
                        apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
                        simp only [Frontend.normalizeChildren?, declarationNormalized, Option.bind_eq_bind, Option.bind_some]
                        rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
