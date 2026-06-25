import Mettapedia.KR.ConceptOntology.BenchmarkControl

-- AUTO-GENERATED from /home/zar/claude/mizar/share/mml/conlat_1.miz. Do not edit by hand.

namespace Mettapedia.KR.ConceptOntology.Generated.MizarConlat1

open Mettapedia.KR.ConceptOntology
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

inductive Item where
  | definition_1 -- definition ::$CD struct (2-sorted) ContextStr (# carrier, carrier' -> set, Information -> Relation of the carrier,the ca
  | registration_2 -- registration cluster strict non empty non void for ContextStr; existence proof ContextStr(#{{}},{{}},the Relation of {{}
  | definition_2 -- definition mode FormalContext is non empty non void ContextStr; end;
  | definition_3 -- definition let C be 2-sorted; mode Object of C is Element of C; mode Attribute of C is Element of the carrier' of C; end
  | registration_4 -- registration let C be non empty non void 2-sorted; cluster non empty for Subset of the carrier of C; existence proof tak
  | definition_4 -- definition let C be FormalContext; let o be Object of C; let a be Attribute of C; pred o is-connected-with a means [o,a]
  | notation_1 -- notation let C be FormalContext; let o be Object of C; let a be Attribute of C; antonym o is-not-connected-with a for o 
  | definition_5 -- definition let C be FormalContext; func ObjectDerivation(C) -> Function of bool the carrier of C,bool the carrier' of C 
  | definition_6 -- definition let C be FormalContext; func AttributeDerivation(C) -> Function of bool the carrier' of C,bool the carrier of
  | theorem_1 -- theorem for C being FormalContext for o being Object of C holds ( ObjectDerivation(C)).({o}) = {a where a is Attribute o
  | theorem_2 -- theorem for C being FormalContext for a being Attribute of C holds ( AttributeDerivation(C)).({a}) = {o where o is Objec
  | theorem_3 -- theorem Th3: for C being FormalContext for O1,O2 being Subset of the carrier of C holds O1 c= O2 implies (ObjectDerivati
  | theorem_4 -- theorem Th4: for C being FormalContext for A1,A2 being Subset of the carrier' of C holds A1 c= A2 implies (AttributeDeri
  | theorem_5 -- theorem Th5: for C being FormalContext for O being Subset of the carrier of C holds O c= (AttributeDerivation(C)).((Obje
  deriving DecidableEq, Repr, Fintype

def itemLabel : Item → String
  | .definition_1 => "definition_1"
  | .registration_2 => "registration_2"
  | .definition_2 => "definition_2"
  | .definition_3 => "definition_3"
  | .registration_4 => "registration_4"
  | .definition_4 => "definition_4"
  | .notation_1 => "notation_1"
  | .definition_5 => "definition_5"
  | .definition_6 => "definition_6"
  | .theorem_1 => "theorem_1"
  | .theorem_2 => "theorem_2"
  | .theorem_3 => "theorem_3"
  | .theorem_4 => "theorem_4"
  | .theorem_5 => "theorem_5"

inductive Attribute where
  | AttributeCtor -- Attribute
  | AttributeDerivation -- AttributeDerivation
  | ContextStr -- ContextStr
  | FormalContext -- FormalContext
  | Function -- Function
  | Information -- Information
  | ObjectDerivation -- ObjectDerivation
  | Subset -- Subset
  | is_connected_with -- is-connected-with
  deriving DecidableEq, Repr, Fintype

def attributeLabel : Attribute → String
  | .AttributeCtor => "Attribute"
  | .AttributeDerivation => "AttributeDerivation"
  | .ContextStr => "ContextStr"
  | .FormalContext => "FormalContext"
  | .Function => "Function"
  | .Information => "Information"
  | .ObjectDerivation => "ObjectDerivation"
  | .Subset => "Subset"
  | .is_connected_with => "is-connected-with"

def evidence : Item → Attribute → BinaryEvidence
  | .definition_1, .ContextStr => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_1, .Information => BinaryFcaBenchmarkContext.supportToken 1
  | .registration_2, .ContextStr => BinaryFcaBenchmarkContext.supportToken 2
  | .definition_2, .ContextStr => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_2, .FormalContext => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_3, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 1
  | .registration_4, .Subset => BinaryFcaBenchmarkContext.supportToken 2
  | .definition_4, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_4, .FormalContext => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_4, .Information => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_4, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 1
  | .notation_1, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 1
  | .notation_1, .FormalContext => BinaryFcaBenchmarkContext.supportToken 1
  | .notation_1, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_5, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 28
  | .definition_5, .FormalContext => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_5, .Function => BinaryFcaBenchmarkContext.supportToken 4
  | .definition_5, .ObjectDerivation => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_5, .Subset => BinaryFcaBenchmarkContext.supportToken 14
  | .definition_5, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 28
  | .definition_6, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 29
  | .definition_6, .AttributeDerivation => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_6, .FormalContext => BinaryFcaBenchmarkContext.supportToken 1
  | .definition_6, .Function => BinaryFcaBenchmarkContext.supportToken 4
  | .definition_6, .Subset => BinaryFcaBenchmarkContext.supportToken 14
  | .definition_6, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 29
  | .theorem_1, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 12
  | .theorem_1, .FormalContext => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_1, .ObjectDerivation => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_1, .Subset => BinaryFcaBenchmarkContext.supportToken 1
  | .theorem_1, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 12
  | .theorem_2, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 9
  | .theorem_2, .AttributeDerivation => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_2, .FormalContext => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_2, .Subset => BinaryFcaBenchmarkContext.supportToken 1
  | .theorem_2, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 12
  | .theorem_3, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 3
  | .theorem_3, .FormalContext => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_3, .ObjectDerivation => BinaryFcaBenchmarkContext.supportToken 3
  | .theorem_3, .Subset => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_3, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 4
  | .theorem_4, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 4
  | .theorem_4, .AttributeDerivation => BinaryFcaBenchmarkContext.supportToken 3
  | .theorem_4, .FormalContext => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_4, .Subset => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_4, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 4
  | .theorem_5, .AttributeCtor => BinaryFcaBenchmarkContext.supportToken 6
  | .theorem_5, .AttributeDerivation => BinaryFcaBenchmarkContext.supportToken 3
  | .theorem_5, .FormalContext => BinaryFcaBenchmarkContext.supportToken 2
  | .theorem_5, .ObjectDerivation => BinaryFcaBenchmarkContext.supportToken 1
  | .theorem_5, .Subset => BinaryFcaBenchmarkContext.supportToken 3
  | .theorem_5, .is_connected_with => BinaryFcaBenchmarkContext.supportToken 5
  | _, _ => (0 : BinaryEvidence)

def context : BinaryFcaBenchmarkContext Item Attribute where
  evidence := evidence

def thresholds : Bool → ℝ≥0∞
  | false => 1
  | true => 2

def gateFamily : Bool → EvidenceGate BinaryEvidence :=
  BinaryFcaBenchmarkContext.thresholdGateFamily thresholds

def exactGate : EvidenceGate BinaryEvidence :=
  BinaryFcaBenchmarkContext.exactGate

end Mettapedia.KR.ConceptOntology.Generated.MizarConlat1
