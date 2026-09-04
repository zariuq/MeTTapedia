/-!
# Semantic symbol identities for TPTP first-order formulae

TPTP gives several concrete symbol classes different meanings.  An ordinary
atomic word, a defined word, a system word, a number, and a distinct object
must therefore not collapse merely because their decoded lexemes coincide.

This module records the class as part of semantic identity while deliberately
forgetting only presentation choices that do not change identity, such as a
plain atomic word being written as a lower word or a quoted word.  Exact source
spelling remains the responsibility of the official abstract syntax; a later
serializer may choose a canonical spelling for the same semantic head.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity

/-- Semantic classes of FOF term heads. -/
inductive FunctionKind where
  | plain
  | defined
  | system
  | integer
  | rational
  | real
  | distinctObject
  deriving DecidableEq, Repr

/-- Semantic classes of FOF predicate heads.  Equality remains a dedicated
formula constructor and is intentionally absent. -/
inductive PredicateKind where
  | plain
  | defined
  | system
  deriving DecidableEq, Repr

structure FunctionHead where
  kind : FunctionKind
  lexeme : String
  deriving DecidableEq, Repr

structure PredicateHead where
  kind : PredicateKind
  lexeme : String
  deriving DecidableEq, Repr

/-- Only ordinary functors belong to TSTP's `principal_symbol` inventory.
Defined, system, numeric, and distinct-object heads remain semantically real,
but are not user-introduced principal symbols. -/
def FunctionHead.principalName? (head : FunctionHead) : Option String :=
  match head.kind with
  | .plain => some head.lexeme
  | _ => none

/-- Only ordinary predicates belong to the user principal-symbol inventory. -/
def PredicateHead.principalName? (head : PredicateHead) : Option String :=
  match head.kind with
  | .plain => some head.lexeme
  | _ => none

namespace Canary

theorem plain_and_integer_with_same_lexeme_are_distinct :
    FunctionHead.mk .plain "2" != FunctionHead.mk .integer "2" := by
  decide

theorem defined_and_system_with_same_lexeme_are_distinct :
    PredicateHead.mk .defined "answer" !=
      PredicateHead.mk .system "answer" := by
  decide

theorem plain_function_is_a_principal_symbol :
    (FunctionHead.mk .plain "f").principalName? = some "f" := by
  rfl

theorem distinct_object_is_not_a_principal_symbol :
    (FunctionHead.mk .distinctObject "object").principalName? = none := by
  rfl

end Canary

#print axioms Canary.plain_and_integer_with_same_lexeme_are_distinct
#print axioms Canary.defined_and_system_with_same_lexeme_are_distinct
#print axioms Canary.plain_function_is_a_principal_symbol
#print axioms Canary.distinct_object_is_not_a_principal_symbol

end Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity
