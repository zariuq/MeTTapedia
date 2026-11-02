import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogLiteralReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogNameMeaning

/-! Meaning of the source-preserving program data at the independent IR
boundary. Literals and names have declared interpretations; all other
constructor fields and fixed vectors retain their order and multiplicity. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

def PlainNode (label : String) (children : List Pattern) : Prop :=
  label ≠ "FloatValue" ∧
  (∀ source, Pattern.apply label children ≠ .apply "SymbolValue" [source]) ∧
  (∀ source, Pattern.apply label children ≠ .apply "IntegerValue" [source]) ∧
  (∀ source, Pattern.apply label children ≠ .apply "UnsignedValue" [source]) ∧
  (∀ source, Pattern.apply label children ≠ .apply "Relation" [source]) ∧
  (∀ source, Pattern.apply label children ≠ .apply "Variable" [source]) ∧
  (∀ source type, Pattern.apply label children ≠ .apply "Attribute" [source,type])

inductive Normalizes : Pattern → Pattern → Prop where
  | literal {label : String} {source : Pattern} {value : Mettapedia.Languages.Datalog.Value} :
      Literal label source value → Normalizes (.apply label [source]) (IRCodec.value value)
  | relation {source : Pattern} {name : List String} : QualifiedName source name →
      Normalizes (.apply "Relation" [source]) (IRCodec.relation name)
  | logical {source : Pattern} {name : String} : Spells source name →
      Normalizes (.apply "Variable" [source]) (.apply "Variable" [IRCodec.atom name])
  | attributeData {source input output : Pattern} {name : String} : Spells source name → Normalizes input output →
      Normalizes (.apply "Attribute" [source,input]) (.apply "Attribute" [IRCodec.atom name,output])
  | node (label : String) (inputs outputs : List Pattern) : PlainNode label inputs →
      List.Forall₂ Normalizes inputs outputs → Normalizes (.apply label inputs) (.apply label outputs)
  | vector (inputs outputs : List Pattern) : List.Forall₂ Normalizes inputs outputs →
      Normalizes (.collection .vec inputs none) (.collection .vec outputs none)

theorem plain_normalization (label : String) (children : List Pattern) (plain : PlainNode label children) :
    Frontend.normalize? (.apply label children) = (Frontend.normalizeChildren? children).map (Pattern.apply label) := by
  unfold Frontend.normalize?
  split <;> simp_all [PlainNode]

mutual
theorem normalization_complete {source target : Pattern} (meaning : Normalizes source target) :
    Frontend.normalize? source = some target := by
  cases meaning with
  | literal literal =>
    cases literal with
    | symbol body => simpa only [Frontend.normalize?] using literal_value_complete (Literal.symbol body)
    | integer source value text spelling digits fits =>
      simpa only [Frontend.normalize?] using literal_value_complete (Literal.integer _ value text spelling digits fits)
    | unsigned source value text spelling digits fits =>
      simpa only [Frontend.normalize?] using literal_value_complete (Literal.unsigned _ value text spelling digits fits)
  | relation spelling => simp [Frontend.normalize?,qualifiedName_complete spelling]
  | logical spelling => simp [Frontend.normalize?,spelling_complete spelling]
  | attributeData spelling child => simp [Frontend.normalize?,spelling_complete spelling,normalization_complete child]
  | node label inputs outputs plain children =>
    rw [plain_normalization label inputs plain,normalization_children_complete children]
    rfl
  | vector inputs outputs children => simp [Frontend.normalize?,normalization_children_complete children]
termination_by sizeOf source

theorem normalization_children_complete {sources targets : List Pattern} (meaning : List.Forall₂ Normalizes sources targets) :
    Frontend.normalizeChildren? sources = some targets := by
  cases meaning with
  | nil => rfl
  | cons first rest => simp [Frontend.normalizeChildren?,normalization_complete first,normalization_children_complete rest]
termination_by sizeOf sources
end

#print axioms plain_normalization
#print axioms normalization_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
