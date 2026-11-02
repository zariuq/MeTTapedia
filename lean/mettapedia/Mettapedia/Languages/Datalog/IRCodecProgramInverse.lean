import Mettapedia.Languages.Datalog.IRCodecScalarInverse

/-! Successful independent program decoding loses no IR structure. The
reverse laws retain literal payloads, variable names, clause order and
duplicate occurrences, complementing the existing encoding round trips. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Datalog.IRCodec

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

theorem qualifiedName_inverse (source : Pattern) (name : QualifiedName) (read : qualifiedName? source = some name) : qualifiedName name = source := by
  unfold qualifiedName? at read
  split at read
  · rename_i parts
    simp only [qualifiedName,vector_inverse atom atom? atom_inverse parts name read]
  · cases read

theorem relation_inverse (source : Pattern) (name : QualifiedName) (read : relation? source = some name) : relation name = source := by
  unfold relation? at read
  split at read
  · rename_i payload
    simp only [relation,qualifiedName_inverse payload name read]
  · cases read

theorem argument_inverse (source : Pattern) (output : Argument) (read : argument? source = some output) : argument output = source := by
  unfold argument? at read
  split at read
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [argument,value_inverse payload input parsed]
  · rename_i name
    obtain ⟨text,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [argument,atom_inverse name text parsed]
  · cases Option.some.inj read
    rfl
  · cases read

theorem tuple_inverse (source : Pattern) (values : List Argument) (read : tuple? source = some values) : tuple values = source := by
  unfold tuple? at read
  split at read
  · rename_i payload
    simp only [tuple,vector_inverse argument argument? argument_inverse payload values read]
  · cases read

theorem groundTuple_inverse (source : Pattern) (values : List Value) (read : groundTuple? source = some values) : groundTuple values = source := by
  unfold groundTuple? at read
  split at read
  · rename_i payload
    simp only [groundTuple,vector_inverse value value? value_inverse payload values read]
  · cases read

theorem positiveAtom_inverse (source : Pattern) (output : Atom) (read : positiveAtom? source = some output) : positiveAtom output = source := by
  unfold positiveAtom? at read
  split at read
  · rename_i name arguments
    change ((relation? name).bind fun relationName => (tuple? arguments).bind fun values =>
      some (⟨relationName,values⟩ : Atom)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨relationName,nameRead,values,valuesRead,rfl⟩ := read
    simp only [positiveAtom,relation_inverse name relationName nameRead,tuple_inverse arguments values valuesRead]
  · cases read

theorem groundFact_inverse (source : Pattern) (output : GroundFact) (read : groundFact? source = some output) : groundFact output = source := by
  unfold groundFact? at read
  split at read
  · rename_i name values
    change ((relation? name).bind fun relationName => (groundTuple? values).bind fun fields =>
      some (⟨relationName,fields⟩ : GroundFact)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨relationName,nameRead,fields,fieldsRead,rfl⟩ := read
    simp only [groundFact,relation_inverse name relationName nameRead,groundTuple_inverse values fields fieldsRead]
  · cases read

theorem operator_inverse (tag : String) (output : ComparisonOperator) (read : operator? tag = some output) : operator output = tag := by
  unfold operator? at read
  split at read <;> first | (cases Option.some.inj read; rfl) | cases read

theorem comparison_inverse (source : Pattern) (output : Comparison) (read : comparison? source = some output) : comparison output = source := by
  unfold comparison? at read
  split at read
  · rename_i tag left right
    change ((operator? tag).bind fun op => (argument? left).bind fun first => (argument? right).bind fun second =>
      some (⟨op,first,second⟩ : Comparison)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨op,opRead,first,leftRead,second,rightRead,rfl⟩ := read
    simp only [comparison,operator_inverse tag op opRead,argument_inverse left first leftRead,argument_inverse right second rightRead]
  · cases read

theorem premise_inverse (source : Pattern) (output : Premise) (read : premise? source = some output) : premise output = source := by
  unfold premise? at read
  split at read
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [premise,comparison_inverse payload input parsed]
  · obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    exact positiveAtom_inverse source input parsed

theorem clause_inverse (source : Pattern) (output : Clause) (read : clause? source = some output) : clause output = source := by
  unfold clause? at read
  split at read
  · rename_i name arguments body
    change ((relation? name).bind fun relationName => (tuple? arguments).bind fun head =>
      (vector? premise? body).bind fun premises => some (⟨⟨relationName,head⟩,premises⟩ : Clause)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨relationName,nameRead,head,headRead,premises,bodyRead,rfl⟩ := read
    simp only [clause,relation_inverse name relationName nameRead,tuple_inverse arguments head headRead,
      vector_inverse premise premise? premise_inverse body premises bodyRead]
  · cases read

theorem attributeType_inverse (source : Pattern) (output : AttributeType) (read : attributeType? source = some output) : attributeType output = source := by
  unfold attributeType? at read
  split at read <;> first | (cases Option.some.inj read; rfl) | cases read

theorem attribute_inverse (source : Pattern) (output : Attribute) (read : attributeData? source = some output) : attributeData output = source := by
  unfold attributeData? at read
  split at read
  · rename_i name type
    change ((atom? name).bind fun identifier => (attributeType? type).bind fun kind =>
      some (⟨identifier,kind⟩ : Attribute)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨identifier,nameRead,kind,typeRead,rfl⟩ := read
    simp only [attributeData,atom_inverse name identifier nameRead,attributeType_inverse type kind typeRead]
  · cases read

theorem declaration_inverse (source : Pattern) (output : RelationDeclaration) (read : declaration? source = some output) : declaration output = source := by
  unfold declaration? at read
  split at read
  · rename_i name attributes
    change ((relation? name).bind fun relationName => (vector? attributeData? attributes).bind fun fields =>
      some (⟨relationName,fields⟩ : RelationDeclaration)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨relationName,nameRead,fields,fieldsRead,rfl⟩ := read
    simp only [declaration,relation_inverse name relationName nameRead,vector_inverse attributeData attributeData? attribute_inverse attributes fields fieldsRead]
  · cases read

theorem statement_inverse (source : Pattern) (output : Statement) (read : statement? source = some output) : statement output = source := by
  unfold statement? at read
  split at read
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [statement,declaration_inverse payload input parsed]
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [statement,clause_inverse payload input parsed]
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [statement,relation_inverse payload input parsed]
  · rename_i payload
    obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [statement,relation_inverse payload input parsed]
  · obtain ⟨input,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    exact groundFact_inverse source input parsed

theorem program_inverse (source : Pattern) (output : Program) (read : program? source = some output) : program output = source := by
  unfold program? at read
  split at read
  · rename_i payload
    obtain ⟨statements,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [program,vector_inverse statement statement? statement_inverse payload statements parsed]
  · cases read

#print axioms program_inverse

end Mettapedia.Languages.Datalog.IRCodec
