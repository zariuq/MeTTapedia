import Mettapedia.GSLT.LanguageDef.StructuredC

/-!
# Compositional builders for StructuredC syntax

`StructuredC` deliberately exposes an ordinary `Pattern` carrier.  This module
provides the small vocabulary needed to assemble that carrier without repeating
constructor spines throughout every lowering.  The builders create syntax only;
sorting and operational adequacy remain independent obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuredC.Builder

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Apply one StructuredC constructor, or form one builtin token when the
argument list is empty. -/
def node (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def token (text : String) : Pattern := node text

def identifier (name : String) : Pattern :=
  node "structured-c:identifier" [token name]

def functionName (name : String) : Pattern :=
  node "structured-c:function-name" [token name]

def externalName (name : String) : Pattern :=
  node "structured-c:external-name" [token name]

def namedType (name : String) : Pattern :=
  node "structured-c:type-named" [identifier name]

def constType (target : Pattern) : Pattern :=
  node "structured-c:type-const" [target]

def pointerType (target : Pattern) : Pattern :=
  node "structured-c:type-pointer" [target]

def namedPointerType (name : String) (isConst : Bool := false) : Pattern :=
  pointerType (if isConst then constType (namedType name) else namedType name)

def valueSymbol (name : String) : Pattern :=
  node "structured-c:value-symbol" [identifier name]

def constant (value : Pattern) : Pattern :=
  node "structured-c:expression-constant" [value]

def symbol (name : String) : Pattern :=
  constant (valueSymbol name)

def variableExpression (name : String) : Pattern :=
  node "structured-c:expression-variable" [identifier name]

def expressions : List Pattern → Pattern
  | [] => node "structured-c:expressions-nil"
  | expression :: rest =>
      node "structured-c:expressions-cons" [expression, expressions rest]

def call (name : String) (arguments : List Pattern := []) : Pattern :=
  node "structured-c:expression-call" [externalName name,
    expressions arguments]

def statements : List Pattern → Pattern
  | [] => node "structured-c:statements-nil"
  | statement :: rest =>
      node "structured-c:statements-cons" [statement, statements rest]

def appendStatements (first second : Pattern) : Pattern :=
  node "structured-c:statements-append" [first, second]

def effect (expression : Pattern) : Pattern :=
  node "structured-c:effect" [expression]

def assign (name : String) (expression : Pattern) : Pattern :=
  node "structured-c:assign" [identifier name, expression]

def declare (name : String) (type expression : Pattern) : Pattern :=
  node "structured-c:declare" [identifier name, type, expression]

def ifThenElse (condition thenBranch elseBranch : Pattern) : Pattern :=
  node "structured-c:if" [condition, thenBranch, elseBranch]

def whileDo (condition body : Pattern) : Pattern :=
  node "structured-c:while" [condition, body]

def returnExpression (expression : Pattern) : Pattern :=
  node "structured-c:return" [expression]

def returnSymbol (name : String) : Pattern :=
  returnExpression (symbol name)

def caseBranch (value body : Pattern) : Pattern :=
  node "structured-c:case" [value, body]

def cases : List Pattern → Pattern
  | [] => node "structured-c:cases-nil"
  | one :: rest => node "structured-c:cases-cons" [one, cases rest]

def switch (scrutinee : Pattern) (branches : List Pattern)
    (defaultBranch : Pattern) : Pattern :=
  node "structured-c:switch" [scrutinee, cases branches, defaultBranch]

def parameter (name : String) (type : Pattern) : Pattern :=
  node "structured-c:parameter" [identifier name, type]

def parameters : List Pattern → Pattern
  | [] => node "structured-c:parameters-nil"
  | one :: rest =>
      node "structured-c:parameters-cons" [one, parameters rest]

def function (name : String) (returnType : Pattern)
    (params : List Pattern) (body : Pattern) : Pattern :=
  node "structured-c:function" [functionName name, returnType,
    parameters params, body]

def externalFunction (name : String) (returnType : Pattern)
    (params : List Pattern) : Pattern :=
  node "structured-c:external-function" [externalName name, returnType,
    parameters params]

def functions : List Pattern → Pattern
  | [] => node "structured-c:functions-nil"
  | one :: rest => node "structured-c:functions-cons" [one, functions rest]

def externalFunctions : List Pattern → Pattern
  | [] => node "structured-c:external-functions-nil"
  | one :: rest =>
      node "structured-c:external-functions-cons" [one,
        externalFunctions rest]

def program (externals functions : List Pattern) : Pattern :=
  node "structured-c:program" [externalFunctions externals,
    Builder.functions functions]

end Mettapedia.GSLT.LanguageDef.StructuredC.Builder
