import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# GF Semantic Kernel in `languageDef!` Form

This module captures the **council-clear** GF semantic kernel as a directly
authored `languageDef!` fragment:

- 1 equation: `UseN(x) = x`
- 10 rewrites: 6 identity eliminations, 1 active/passive entailment,
  3 tense rewrites

It is intentionally a **semantic fragment**, not the full runtime-loaded GF
grammar. The full constructor inventory still comes from `GFCore.GrammarSig`;
this module exists to make the semantic kernel readable, reviewable, and
reusable from the shared Lean `languageDef!` surface.
-/

namespace Mettapedia.Languages.GF.SemanticKernelDSL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Authored GF semantic kernel fragment. Terms are intentionally omitted here:
    the full GF constructor inventory is provided dynamically by `GFCore`.
    This fragment is the semantic rule inventory only. -/
def gfSemanticKernelLanguageDef : LanguageDef :=
  languageDef! {
    name : "GFSemanticKernel"
    types {
      S
      Cl
      NP
      VP
      N
      A
      Comp
      V
      N2
      A2
      V2
      Tense
      Ant
      Pol
    }
    terms { }
    equations {
      UseNIdentity . x:N |- UseN(x) = x;
    }
    rewrites {
      UseNElim . x:N |- UseN(x) ~> x;
      PositAElim . x:A |- PositA(x) ~> x;
      UseCompElim . x:Comp |- UseComp(x) ~> x;
      UseVElim . x:V |- UseV(x) ~> x;
      UseN2Elim . x:N2 |- UseN2(x) ~> x;
      UseA2Elim . x:A2 |- UseA2(x) ~> x;
      ActivePassive . v:V2, np1:NP, np2:NP |- PredVP(np1, ComplSlash(SlashV2a(v), np2)) ~> PredVP(np2, PassV2(v));
      PresentTense . cl:Cl |- UseCl(TTAnt("TPres", "ASimul"), "PPos", cl) ~> "⊛temporal"(cl, "0");
      PastTense . cl:Cl |- UseCl(TTAnt("TPast", "ASimul"), "PPos", cl) ~> "⊛temporal"(cl, "-1");
      FutureTense . cl:Cl |- UseCl(TTAnt("TFut", "ASimul"), "PPos", cl) ~> "⊛temporal"(cl, "1");
    }
    logic { }
    oracles { }
    congruenceCollections { }
  }

private def equationAt (i : Nat) (h : i < gfSemanticKernelLanguageDef.equations.length) : Equation :=
  gfSemanticKernelLanguageDef.equations.get ⟨i, h⟩

private def rewriteAt (i : Nat) (h : i < gfSemanticKernelLanguageDef.rewrites.length) : RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites.get ⟨i, h⟩

def useNIdentityEquation : Equation :=
  equationAt 0 (by native_decide)

def useNElimRewrite : RewriteRule :=
  rewriteAt 0 (by native_decide)

def positAElimRewrite : RewriteRule :=
  rewriteAt 1 (by native_decide)

def useCompElimRewrite : RewriteRule :=
  rewriteAt 2 (by native_decide)

def useVElimRewrite : RewriteRule :=
  rewriteAt 3 (by native_decide)

def useN2ElimRewrite : RewriteRule :=
  rewriteAt 4 (by native_decide)

def useA2ElimRewrite : RewriteRule :=
  rewriteAt 5 (by native_decide)

def activePassiveRewrite : RewriteRule :=
  rewriteAt 6 (by native_decide)

def presentTenseRewrite : RewriteRule :=
  rewriteAt 7 (by native_decide)

def pastTenseRewrite : RewriteRule :=
  rewriteAt 8 (by native_decide)

def futureTenseRewrite : RewriteRule :=
  rewriteAt 9 (by native_decide)

def allIdentityRewrites : List RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites.take 6

def allTenseRewrites : List RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites.drop 7

def allSemanticRewrites : List RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites

example : gfSemanticKernelLanguageDef.equations.length = 1 := rfl
example : gfSemanticKernelLanguageDef.rewrites.length = 10 := rfl
example : allIdentityRewrites.length = 6 := by native_decide
example : allTenseRewrites.length = 3 := by native_decide
example : allSemanticRewrites.length = 10 := rfl
example : useNIdentityEquation.name = "UseNIdentity" := rfl
example : activePassiveRewrite.name = "ActivePassive" := rfl
example : presentTenseRewrite.name = "PresentTense" := rfl
example : pastTenseRewrite.name = "PastTense" := rfl
example : futureTenseRewrite.name = "FutureTense" := rfl

end Mettapedia.Languages.GF.SemanticKernelDSL
