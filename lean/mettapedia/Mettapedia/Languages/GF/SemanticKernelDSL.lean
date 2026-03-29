import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# GF Semantic Kernel in `languageDef!` Form

This module captures the **council-clear** GF semantic kernel as a directly
authored `languageDef!` fragment:

- 1 equation: `UseN(x) = x`
- 44 rewrites in 11 families: 10 identity, 2 voice, 3 tense,
  3 negation, 5 embedding, 1 subordination, 4 completion,
  5 coordination, 3 relative clause, 4 aspect, 4 quantifier

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
      SC
      Cl
      NP
      VP
      VPSlash
      N
      A
      AP
      Comp
      V
      N2
      A2
      V2
      VV
      VS
      VQ
      VA
      QS
      PN
      Pron
      Tense
      Ant
      Pol
      Subj
      Adv
      Conj
      ListS
      ListNP
      ListAP
      ListAdv
      ListCN
      RS
      RCl
      RP
      Det
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
      NegationPresent . cl:Cl |- UseCl(TTAnt("TPres", "ASimul"), "PNeg", cl) ~> "⊛negation"("⊛temporal"(cl, "0"));
      NegationPast . cl:Cl |- UseCl(TTAnt("TPast", "ASimul"), "PNeg", cl) ~> "⊛negation"("⊛temporal"(cl, "-1"));
      NegationFuture . cl:Cl |- UseCl(TTAnt("TFut", "ASimul"), "PNeg", cl) ~> "⊛negation"("⊛temporal"(cl, "1"));
      EmbedPresent . cl:Cl |- EmbedS(UseCl(TTAnt("TPres", "ASimul"), "PPos", cl)) ~> "⊛embedded"(cl);
      EmbedPast . cl:Cl |- EmbedS(UseCl(TTAnt("TPast", "ASimul"), "PPos", cl)) ~> "⊛embedded"(cl);
      EmbedFuture . cl:Cl |- EmbedS(UseCl(TTAnt("TFut", "ASimul"), "PPos", cl)) ~> "⊛embedded"(cl);
      UsePNElim . x:PN |- UsePN(x) ~> x;
      UsePronElim . x:Pron |- UsePron(x) ~> x;
      MassNPElim . x:CN |- MassNP(x) ~> x;
      ProDropElim . x:Pron |- ProDrop(x) ~> x;
      ReflVPElim . x:VPSlash |- ReflVP(x) ~> x;
      EmbedVPLifting . vp:VP |- EmbedVP(vp) ~> "⊛embedded"(vp);
      EmbedQSLifting . qs:QS |- EmbedQS(qs) ~> "⊛question"(qs);
      SubjSAdverb . subj:Subj, s:S |- SubjS(subj, s) ~> "⊛subordinate"(s, subj);
      ComplVVElim . vv:VV, vp:VP |- ComplVV(vv, vp) ~> vp;
      ComplVSElim . vs:VS, s:S |- ComplVS(vs, s) ~> s;
      ComplVQElim . vq:VQ, qs:QS |- ComplVQ(vq, qs) ~> qs;
      ComplVAElim . va:VA, ap:AP |- ComplVA(va, ap) ~> ap;
      ConjSBinary . conj:Conj, s1:S, s2:S |- ConjS(conj, BaseS(s1, s2)) ~> "⊛conjunction"(conj, s1, s2);
      ConjNPBinary . conj:Conj, np1:NP, np2:NP |- ConjNP(conj, BaseNP(np1, np2)) ~> "⊛conjunction"(conj, np1, np2);
      ConjAPBinary . conj:Conj, ap1:AP, ap2:AP |- ConjAP(conj, BaseAP(ap1, ap2)) ~> "⊛conjunction"(conj, ap1, ap2);
      ConjAdvBinary . conj:Conj, adv1:Adv, adv2:Adv |- ConjAdv(conj, BaseAdv(adv1, adv2)) ~> "⊛conjunction"(conj, adv1, adv2);
      ConjCNBinary . conj:Conj, cn1:CN, cn2:CN |- ConjCN(conj, BaseCN(cn1, cn2)) ~> "⊛conjunction"(conj, cn1, cn2);
      RelVPSubject . vp:VP |- RelVP("IdRP", vp) ~> "⊛relative"(vp);
      RelCNModify . cn:CN, rs:RS |- RelCN(cn, rs) ~> "⊛modified"(cn, rs);
      RelClBase . cl:Cl |- RelCl(cl) ~> "⊛relclause"(cl);
      AnteriorPresent . cl:Cl |- UseCl(TTAnt("TPres", "AAnter"), "PPos", cl) ~> "⊛anterior"("⊛temporal"(cl, "0"));
      AnteriorPast . cl:Cl |- UseCl(TTAnt("TPast", "AAnter"), "PPos", cl) ~> "⊛anterior"("⊛temporal"(cl, "-1"));
      ConditionalSimul . cl:Cl |- UseCl(TTAnt("TCond", "ASimul"), "PPos", cl) ~> "⊛conditional"("⊛temporal"(cl, "?"));
      ConditionalAnter . cl:Cl |- UseCl(TTAnt("TCond", "AAnter"), "PPos", cl) ~> "⊛anterior"("⊛conditional"("⊛temporal"(cl, "?")));
      DetEveryElim . cn:CN |- DetCN("every_Det", cn) ~> "⊛universal"(cn);
      DetSomeElim . cn:CN |- DetCN("someSg_Det", cn) ~> "⊛existential"(cn);
      DetTheElim . cn:CN |- DetCN("the_Det", cn) ~> "⊛definite"(cn);
      DetNoElim . cn:CN |- DetCN("no_Det", cn) ~> "⊛negUniversal"(cn);
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
  equationAt 0 (by decide)

def useNElimRewrite : RewriteRule :=
  rewriteAt 0 (by decide)

def positAElimRewrite : RewriteRule :=
  rewriteAt 1 (by decide)

def useCompElimRewrite : RewriteRule :=
  rewriteAt 2 (by decide)

def useVElimRewrite : RewriteRule :=
  rewriteAt 3 (by decide)

def useN2ElimRewrite : RewriteRule :=
  rewriteAt 4 (by decide)

def useA2ElimRewrite : RewriteRule :=
  rewriteAt 5 (by decide)

def activePassiveRewrite : RewriteRule :=
  rewriteAt 6 (by decide)

def presentTenseRewrite : RewriteRule :=
  rewriteAt 7 (by decide)

def pastTenseRewrite : RewriteRule :=
  rewriteAt 8 (by decide)

def futureTenseRewrite : RewriteRule :=
  rewriteAt 9 (by decide)

def negationPresentRewrite : RewriteRule :=
  rewriteAt 10 (by decide)

def negationPastRewrite : RewriteRule :=
  rewriteAt 11 (by decide)

def negationFutureRewrite : RewriteRule :=
  rewriteAt 12 (by decide)

def embedPresentRewrite : RewriteRule :=
  rewriteAt 13 (by decide)

def embedPastRewrite : RewriteRule :=
  rewriteAt 14 (by decide)

def embedFutureRewrite : RewriteRule :=
  rewriteAt 15 (by decide)

def allIdentityRewrites : List RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites.take 6

def allTenseRewrites : List RewriteRule :=
  [presentTenseRewrite, pastTenseRewrite, futureTenseRewrite]

def allNegationRewrites : List RewriteRule :=
  [negationPresentRewrite, negationPastRewrite, negationFutureRewrite]

def usePNElimRewrite : RewriteRule :=
  rewriteAt 16 (by decide)
def usePronElimRewrite : RewriteRule :=
  rewriteAt 17 (by decide)
def massNPElimRewrite : RewriteRule :=
  rewriteAt 18 (by decide)
def proDropElimRewrite : RewriteRule :=
  rewriteAt 19 (by decide)
def reflVPElimRewrite : RewriteRule :=
  rewriteAt 20 (by decide)
def embedVPLiftingRewrite : RewriteRule :=
  rewriteAt 21 (by decide)
def embedQSLiftingRewrite : RewriteRule :=
  rewriteAt 22 (by decide)
def subjSAdverbRewrite : RewriteRule :=
  rewriteAt 23 (by decide)
def complVVElimRewrite : RewriteRule :=
  rewriteAt 24 (by decide)
def complVSElimRewrite : RewriteRule :=
  rewriteAt 25 (by decide)
def complVQElimRewrite : RewriteRule :=
  rewriteAt 26 (by decide)
def complVAElimRewrite : RewriteRule :=
  rewriteAt 27 (by decide)

def allEmbeddingRewrites : List RewriteRule :=
  [embedPresentRewrite, embedPastRewrite, embedFutureRewrite,
   embedVPLiftingRewrite, embedQSLiftingRewrite]

def allCompletionRewrites : List RewriteRule :=
  [complVVElimRewrite, complVSElimRewrite, complVQElimRewrite, complVAElimRewrite]

def allSubordinationRewrites : List RewriteRule :=
  [subjSAdverbRewrite]

def conjSBinaryRewrite : RewriteRule :=
  rewriteAt 28 (by decide)
def conjNPBinaryRewrite : RewriteRule :=
  rewriteAt 29 (by decide)
def conjAPBinaryRewrite : RewriteRule :=
  rewriteAt 30 (by decide)
def conjAdvBinaryRewrite : RewriteRule :=
  rewriteAt 31 (by decide)
def conjCNBinaryRewrite : RewriteRule :=
  rewriteAt 32 (by decide)
def relVPSubjectRewrite : RewriteRule :=
  rewriteAt 33 (by decide)
def relCNModifyRewrite : RewriteRule :=
  rewriteAt 34 (by decide)
def relClBaseRewrite : RewriteRule :=
  rewriteAt 35 (by decide)
def anteriorPresentRewrite : RewriteRule :=
  rewriteAt 36 (by decide)
def anteriorPastRewrite : RewriteRule :=
  rewriteAt 37 (by decide)
def conditionalSimulRewrite : RewriteRule :=
  rewriteAt 38 (by decide)
def conditionalAnterRewrite : RewriteRule :=
  rewriteAt 39 (by decide)

def allCoordinationRewrites : List RewriteRule :=
  [conjSBinaryRewrite, conjNPBinaryRewrite, conjAPBinaryRewrite,
   conjAdvBinaryRewrite, conjCNBinaryRewrite]

def allRelativeRewrites : List RewriteRule :=
  [relVPSubjectRewrite, relCNModifyRewrite, relClBaseRewrite]

def allAspectRewrites : List RewriteRule :=
  [anteriorPresentRewrite, anteriorPastRewrite,
   conditionalSimulRewrite, conditionalAnterRewrite]

def detEveryElimRewrite : RewriteRule :=
  rewriteAt 40 (by decide)
def detSomeElimRewrite : RewriteRule :=
  rewriteAt 41 (by decide)
def detTheElimRewrite : RewriteRule :=
  rewriteAt 42 (by decide)
def detNoElimRewrite : RewriteRule :=
  rewriteAt 43 (by decide)

def allQuantifierRewrites : List RewriteRule :=
  [detEveryElimRewrite, detSomeElimRewrite, detTheElimRewrite, detNoElimRewrite]

def allSemanticRewrites : List RewriteRule :=
  gfSemanticKernelLanguageDef.rewrites

example : gfSemanticKernelLanguageDef.equations.length = 1 := rfl
example : gfSemanticKernelLanguageDef.rewrites.length = 44 := rfl
example : allQuantifierRewrites.length = 4 := by decide
example : allIdentityRewrites.length = 6 := by decide
example : allTenseRewrites.length = 3 := by decide
example : allNegationRewrites.length = 3 := by decide
example : allEmbeddingRewrites.length = 5 := by decide
example : allCompletionRewrites.length = 4 := by decide
example : allSubordinationRewrites.length = 1 := by decide
example : allCoordinationRewrites.length = 5 := by decide
example : allRelativeRewrites.length = 3 := by decide
example : allAspectRewrites.length = 4 := by decide
example : allSemanticRewrites.length = 44 := rfl

end Mettapedia.Languages.GF.SemanticKernelDSL
