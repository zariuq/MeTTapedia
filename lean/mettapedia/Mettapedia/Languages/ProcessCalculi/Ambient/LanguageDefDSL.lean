import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Ambient Calculus in `languageDef!` Form

This module is the Lean `languageDef!` acceptance test corresponding to the
Rust `language!` definition in
`hyperon/mettail-rust/languages/src/ambient.rs`.

Positive example:
- single-binder `PNew`, collection-rest freshness, and nested process rewrite
  patterns are authored directly in the unified DSL.

Negative example:
- this is a pure process-calculus slice only; it does not claim any extra host
  runtime features beyond what the Rust Ambient language already uses.

The kernel checks the equation indices and the shapes of the authored equations. The declaration gate and the
exported text are checked by evaluation (`#guard`): the gate reads binder names through functions defined by
well-founded recursion, and the text checks search strings, neither of which the kernel unfolds.
-/

namespace Mettapedia.Languages.ProcessCalculi.Ambient.LanguageDefDSL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

private def hasSubstring (needle haystack : String) : Bool :=
  haystack.contains needle

/-- Direct Lean twin of the Rust Ambient `language!` definition. -/
def ambientCore : LanguageDef :=
  languageDef! {
    name : "Ambient"
    types {
      Proc
      Name
    }
    terms {
      PZero . |- "0" : Proc;
      PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc;
      POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc;
      POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc;
      PAmb . n:Name, p:Proc |- n "[" p "]" : Proc;
      PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
    }
    equations {
      NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
      ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
      InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
      OutNew . | x # P |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
      OpenNew . | x # P |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
      AmbNew . | x # P |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
    }
    rewrites {
      InRule . |- (PPar {(PAmb N (PPar {(PIn M P), ...rest1})), (PAmb M R), ...rest2})
        ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2});
      OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
        ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2});
      OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
        ~> (PPar {P, Q, ...rest});
      ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
      NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T);
      AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);
    }
  }

def exportedRustSyntax : String :=
  renderLanguageWithUserSyntax ambientCore

private def newCommEq : Equation :=
  ambientCore.equations.get ⟨0, by decide⟩

private def scopeExtrusionEq : Equation :=
  ambientCore.equations.get ⟨1, by decide⟩

private def inNewEq : Equation :=
  ambientCore.equations.get ⟨2, by decide⟩

private def inNewHasStructuredPrefixApps : Bool :=
  match inNewEq.left, inNewEq.right with
  | .apply "PIn" [.fvar "N", .apply "PNew" [.lambda (some "x") (.fvar "P")]],
    .apply "PNew" [.lambda (some "x") (.apply "PIn" [.fvar "N", .fvar "P"])] => true
  | _, _ => false

private def newCommPreservesBinderOrder : Bool :=
  match newCommEq.left, newCommEq.right with
  | .apply "PNew" [.lambda (some "x") (.apply "PNew" [.lambda (some "y") (.fvar "P")])],
    .apply "PNew" [.lambda (some "y") (.apply "PNew" [.lambda (some "x") (.fvar "P")])] => true
  | _, _ => false

private def scopeExtrusionHasFreshnessAndRest : Bool :=
  match scopeExtrusionEq.premises, scopeExtrusionEq.left, scopeExtrusionEq.right with
  | [.freshness fc],
    .apply "PPar" [.collection .hashBag [.apply "PNew" [.lambda (some "x") (.fvar "P")]] (some "rest")],
    .apply "PNew" [.lambda (some "x") (.apply "PPar" [.collection .hashBag [.fvar "P"] (some "rest")])] =>
      fc.varName == "x" && fc.term == .collection .hashBag [] (some "rest")
  | _, _, _ => false

#guard (LanguageDef.validate ambientCore).isEmpty

example : ambientCore.terms.length = 7 := rfl
example : ambientCore.equations.length = 6 := rfl
example : ambientCore.rewrites.length = 6 := rfl
example : (ambientCore.rewrites.flatMap compileRuleContexts).length = 3 := by
  decide +kernel
example : newCommPreservesBinderOrder = true := by
  decide +kernel
example : scopeExtrusionHasFreshnessAndRest = true := by
  decide +kernel
example : inNewHasStructuredPrefixApps = true := by
  decide +kernel

#guard hasSubstring "name: Ambient" exportedRustSyntax

#guard hasSubstring "PNew . ^x.p:[Name -> Proc] |- \"new\" \"(\" x \",\" p \")\" : Proc;" exportedRustSyntax

#guard hasSubstring "ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));"
  exportedRustSyntax

#guard hasSubstring "InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));" exportedRustSyntax

#guard hasSubstring "OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest});"
  exportedRustSyntax

#guard hasSubstring "AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);" exportedRustSyntax

end Mettapedia.Languages.ProcessCalculi.Ambient.LanguageDefDSL
