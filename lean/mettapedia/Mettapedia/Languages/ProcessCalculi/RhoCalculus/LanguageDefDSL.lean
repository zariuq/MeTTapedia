import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# RhoCalc Process Fragment in `languageDef!` Form

This module is the honest Lean `languageDef!` pressure test against the Rust
`language!` definition in `/home/zar/claude/hyperon/mettail-rust/languages/src/rhocalc.rs`.

Positive example:
- the direct process fragment terms and process-calculus equations/rewrites are
  authored in the same readable style as Rust: `PPar`, `PInputs`, `PNew`,
  `QuoteDrop`, `Extrude`, `Comm`, `Exec`, `ParCong`, `NewCong`.

Negative example:
- this is still not the full Rust `RhoCalc`. We intentionally omit the native
  arithmetic/string fold terms because Lean's authored term DSL does not yet
  carry native term bodies.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Export
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- The directly authored process-calculus fragment of Rust `RhoCalc` that Lean
    can express today without hiding semantics in strings or helper ASTs. -/
def rhoCalcProcessCore : LanguageDef :=
  languageDef! {
    name : "RhoCalc"
    types {
      Proc
      Name
    }
    terms {
      PZero . |- "{}" : Proc;
      PDrop . n:Name |- "*" "(" n ")" : Proc;
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
      POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
      PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns, xs).*map(|n, x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
      NQuote . p:Proc |- "@" "(" p ")" : Name;
      PNew . ^[xs].p:[Name* -> Proc]
        |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
    }
    equations {
      QuoteDrop . |- (NQuote (PDrop N)) = N;
      Extrude . xs.*map(|x| x # ...rest)
        |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}));
    }
    rewrites {
      Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
        ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
      Exec . |- (PDrop (NQuote P)) ~> P;
      ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
      NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);
    }
    logic { }
    oracles { }
    congruenceCollections { HashBag }
  }

abbrev rhoCalcProcessFragment : LanguageDef := rhoCalcProcessCore

private def hasSubstring (needle haystack : String) : Bool :=
  haystack.contains needle

def exportedRustSurface : String :=
  renderLanguageWithUserSyntax rhoCalcProcessCore

example : LanguageDef.validate rhoCalcProcessCore = [] := by
  native_decide

example : rhoCalcProcessCore.terms.length = 7 := rfl
example : rhoCalcProcessCore.equations.length = 2 := rfl
example : rhoCalcProcessCore.rewrites.length = 4 := rfl
example : rhoCalcProcessCore.congruenceCollections = [.hashBag] := rfl

example :
    hasSubstring "name: RhoCalc" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "PZero . |- \"{}\" : Proc;" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc;"
      exportedRustSurface = true := by
  native_decide

example :
    hasSubstring
        "PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- \"(\" *zip(ns, xs).*map(|n, x| n \"?\" x).*sep(\",\") \")\" \".\" \"{\" p \"}\" : Proc;"
        exportedRustSurface = true := by
  native_decide

example :
    hasSubstring
        "PNew . ^[xs].p:[Name* -> Proc] |- \"new\" \"(\" xs.*sep(\",\") \")\" \"in\" \"{\" p \"}\" : Proc;"
        exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "QuoteDrop . |- (NQuote (PDrop N)) = N;" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring
        "Extrude . | xs.*map(|x| x # ...rest) |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}));"
        exportedRustSurface = true := by
  native_decide

example :
    hasSubstring
        "Comm . |- (PPar {(PInputs ns cont), *zip(ns, qs).*map(|n, q| (POutput n q)), ...rest}) ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});"
        exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "Exec . |- (PDrop (NQuote P)) ~> P;" exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});"
      exportedRustSurface = true := by
  native_decide

example :
    hasSubstring "NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);"
      exportedRustSurface = true := by
  native_decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL
