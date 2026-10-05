import Mettapedia.Languages.VibeITP.Presentation.Syntax

/-!
# Vibe-ITP presentation: the kernel rule package

Every judgment of the Vibe-ITP kernel is presented as first-order inference
rules over the data constructors of `Syntax`.  The rules follow the kernel's
own algorithms, including the traversal pruning and the word-bound checks that
decide when the kernel refuses an operation:

* arithmetic on binary numerals (successor, addition, multiplication, order,
  division with remainder, reduction modulo `2 ^ 64`, the machine-word bound);
* term formation, including the depth and free-variable annotations every
  term carries;
* shifting, plugging arguments for bound variables, and instantiating a free
  variable;
* the number literals of the kernel;
* modus ponens, instantiation, and the literal theorems;
* admissibility of a definition by a closed body.

Axioms, definitions, and allocated symbols are not part of this fixed package;
the protocol admits them as additional zero-premise rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-- A rule metavariable. -/
def mv (x : String) : Pattern := .fvar x

/-- A first-order rule with depth-zero metavariables. -/
def mkRule (id : String) (vars : List String) (premises : List Pattern)
    (conclusion : Pattern) : FORule :=
  ⟨id, vars, premises, conclusion⟩

/-! ## Binary numerals -/

def rPsucc1 : FORule :=
  mkRule "vibe-psucc-1" [] [] (jPSucc cP1 (cPO cP1))

def rPsuccO : FORule :=
  mkRule "vibe-psucc-o" ["p"] [] (jPSucc (cPO (mv "p")) (cPI (mv "p")))

def rPsuccI : FORule :=
  mkRule "vibe-psucc-i" ["p", "q"] [jPSucc (mv "p") (mv "q")]
    (jPSucc (cPI (mv "p")) (cPO (mv "q")))

def psuccRules : List FORule :=
  [rPsucc1, rPsuccO, rPsuccI]

def rPadd1l : FORule :=
  mkRule "vibe-padd-1l" ["q", "r"] [jPSucc (mv "q") (mv "r")] (jPAdd cP1 (mv "q") (mv "r"))

def rPadd1r : FORule :=
  mkRule "vibe-padd-1r" ["p", "r"] [jPSucc (mv "p") (mv "r")] (jPAdd (mv "p") cP1 (mv "r"))

def rPaddOo : FORule :=
  mkRule "vibe-padd-oo" ["p", "q", "r"] [jPAdd (mv "p") (mv "q") (mv "r")]
    (jPAdd (cPO (mv "p")) (cPO (mv "q")) (cPO (mv "r")))

def rPaddOi : FORule :=
  mkRule "vibe-padd-oi" ["p", "q", "r"] [jPAdd (mv "p") (mv "q") (mv "r")]
    (jPAdd (cPO (mv "p")) (cPI (mv "q")) (cPI (mv "r")))

def rPaddIo : FORule :=
  mkRule "vibe-padd-io" ["p", "q", "r"] [jPAdd (mv "p") (mv "q") (mv "r")]
    (jPAdd (cPI (mv "p")) (cPO (mv "q")) (cPI (mv "r")))

def rPaddIi : FORule :=
  mkRule "vibe-padd-ii" ["p", "q", "r"] [jPAddC (mv "p") (mv "q") (mv "r")]
    (jPAdd (cPI (mv "p")) (cPI (mv "q")) (cPO (mv "r")))

def paddRules : List FORule :=
  [rPadd1l, rPadd1r, rPaddOo, rPaddOi, rPaddIo, rPaddIi]

def rPaddc11 : FORule :=
  mkRule "vibe-paddc-11" [] [] (jPAddC cP1 cP1 (cPI cP1))

def rPaddc1o : FORule :=
  mkRule "vibe-paddc-1o" ["q", "r"] [jPSucc (mv "q") (mv "r")]
    (jPAddC cP1 (cPO (mv "q")) (cPO (mv "r")))

def rPaddc1i : FORule :=
  mkRule "vibe-paddc-1i" ["q", "r"] [jPSucc (mv "q") (mv "r")]
    (jPAddC cP1 (cPI (mv "q")) (cPI (mv "r")))

def rPaddcO1 : FORule :=
  mkRule "vibe-paddc-o1" ["p", "r"] [jPSucc (mv "p") (mv "r")]
    (jPAddC (cPO (mv "p")) cP1 (cPO (mv "r")))

def rPaddcI1 : FORule :=
  mkRule "vibe-paddc-i1" ["p", "r"] [jPSucc (mv "p") (mv "r")]
    (jPAddC (cPI (mv "p")) cP1 (cPI (mv "r")))

def rPaddcOo : FORule :=
  mkRule "vibe-paddc-oo" ["p", "q", "r"] [jPAdd (mv "p") (mv "q") (mv "r")]
    (jPAddC (cPO (mv "p")) (cPO (mv "q")) (cPI (mv "r")))

def rPaddcOi : FORule :=
  mkRule "vibe-paddc-oi" ["p", "q", "r"] [jPAddC (mv "p") (mv "q") (mv "r")]
    (jPAddC (cPO (mv "p")) (cPI (mv "q")) (cPO (mv "r")))

def rPaddcIo : FORule :=
  mkRule "vibe-paddc-io" ["p", "q", "r"] [jPAddC (mv "p") (mv "q") (mv "r")]
    (jPAddC (cPI (mv "p")) (cPO (mv "q")) (cPO (mv "r")))

def rPaddcIi : FORule :=
  mkRule "vibe-paddc-ii" ["p", "q", "r"] [jPAddC (mv "p") (mv "q") (mv "r")]
    (jPAddC (cPI (mv "p")) (cPI (mv "q")) (cPI (mv "r")))

def paddcRules : List FORule :=
  [rPaddc11, rPaddc1o, rPaddc1i, rPaddcO1, rPaddcI1, rPaddcOo, rPaddcOi, rPaddcIo, rPaddcIi]

def rNadd0l : FORule :=
  mkRule "vibe-nadd-0l" ["b"] [] (jNAdd cN0 (mv "b") (mv "b"))

def rNadd0r : FORule :=
  mkRule "vibe-nadd-0r" ["p"] [] (jNAdd (cNPos (mv "p")) cN0 (cNPos (mv "p")))

def rNaddPp : FORule :=
  mkRule "vibe-nadd-pp" ["p", "q", "r"] [jPAdd (mv "p") (mv "q") (mv "r")]
    (jNAdd (cNPos (mv "p")) (cNPos (mv "q")) (cNPos (mv "r")))

def naddRules : List FORule :=
  [rNadd0l, rNadd0r, rNaddPp]

def rNlt : FORule :=
  mkRule "vibe-nlt" ["a", "p", "b"] [jNAdd (mv "a") (cNPos (mv "p")) (mv "b")]
    (jNLt (mv "a") (mv "b"))

def rNle : FORule :=
  mkRule "vibe-nle" ["a", "c", "b"] [jNAdd (mv "a") (mv "c") (mv "b")]
    (jNLe (mv "a") (mv "b"))

def rNmonusLe : FORule :=
  mkRule "vibe-nmonus-le" ["a", "b"] [jNLe (mv "a") (mv "b")] (jNMonus (mv "a") (mv "b") cN0)

def rNmonusGt : FORule :=
  mkRule "vibe-nmonus-gt" ["a", "b", "p"] [jNAdd (mv "b") (cNPos (mv "p")) (mv "a")]
    (jNMonus (mv "a") (mv "b") (cNPos (mv "p")))

def rNmaxLe : FORule :=
  mkRule "vibe-nmax-le" ["a", "b"] [jNLe (mv "a") (mv "b")] (jNMax (mv "a") (mv "b") (mv "b"))

def rNmaxGt : FORule :=
  mkRule "vibe-nmax-gt" ["a", "b"] [jNLt (mv "b") (mv "a")] (jNMax (mv "a") (mv "b") (mv "a"))

def rBorFf : FORule :=
  mkRule "vibe-bor-ff" [] [] (jBOr cFalse cFalse cFalse)

def rBorFt : FORule :=
  mkRule "vibe-bor-ft" [] [] (jBOr cFalse cTrue cTrue)

def rBorTf : FORule :=
  mkRule "vibe-bor-tf" [] [] (jBOr cTrue cFalse cTrue)

def rBorTt : FORule :=
  mkRule "vibe-bor-tt" [] [] (jBOr cTrue cTrue cTrue)

def orderRules : List FORule :=
  [rNlt, rNle, rNmonusLe, rNmonusGt, rNmaxLe, rNmaxGt, rBorFf, rBorFt, rBorTf, rBorTt]

def rPbits1 : FORule :=
  mkRule "vibe-pbits-1" ["u"] [] (jPBits cP1 (cUS (mv "u")))

def rPbitsO : FORule :=
  mkRule "vibe-pbits-o" ["p", "u"] [jPBits (mv "p") (mv "u")]
    (jPBits (cPO (mv "p")) (cUS (mv "u")))

def rPbitsI : FORule :=
  mkRule "vibe-pbits-i" ["p", "u"] [jPBits (mv "p") (mv "u")]
    (jPBits (cPI (mv "p")) (cUS (mv "u")))

def rNword0 : FORule :=
  mkRule "vibe-nword-0" [] [] (jNWord cN0)

def rNwordP : FORule :=
  mkRule "vibe-nword-p" ["p"] [jPBits (mv "p") patWordBits] (jNWord (cNPos (mv "p")))

def wordRules : List FORule :=
  [rPbits1, rPbitsO, rPbitsI, rNword0, rNwordP]

def rPmul1 : FORule :=
  mkRule "vibe-pmul-1" ["q"] [] (jPMul cP1 (mv "q") (mv "q"))

def rPmulO : FORule :=
  mkRule "vibe-pmul-o" ["p", "q", "r"] [jPMul (mv "p") (mv "q") (mv "r")]
    (jPMul (cPO (mv "p")) (mv "q") (cPO (mv "r")))

def rPmulI : FORule :=
  mkRule "vibe-pmul-i" ["p", "q", "r", "s"]
    [jPMul (mv "p") (mv "q") (mv "r"), jPAdd (cPO (mv "r")) (mv "q") (mv "s")]
    (jPMul (cPI (mv "p")) (mv "q") (mv "s"))

def rNmul0l : FORule :=
  mkRule "vibe-nmul-0l" ["b"] [] (jNMul cN0 (mv "b") cN0)

def rNmul0r : FORule :=
  mkRule "vibe-nmul-0r" ["p"] [] (jNMul (cNPos (mv "p")) cN0 cN0)

def rNmulPp : FORule :=
  mkRule "vibe-nmul-pp" ["p", "q", "r"] [jPMul (mv "p") (mv "q") (mv "r")]
    (jNMul (cNPos (mv "p")) (cNPos (mv "q")) (cNPos (mv "r")))

def rNdivmod : FORule :=
  mkRule "vibe-ndivmod" ["a", "b", "q", "r", "m"]
    [jNMul (mv "b") (mv "q") (mv "m"), jNAdd (mv "m") (mv "r") (mv "a"), jNLt (mv "r") (mv "b")]
    (jNDivMod (mv "a") (mv "b") (mv "q") (mv "r"))

def rNmod64 : FORule :=
  mkRule "vibe-nmod64" ["a", "q", "c"] [jNDivMod (mv "a") patTwo64 (mv "q") (mv "c")]
    (jNMod64 (mv "a") (mv "c"))

def mulRules : List FORule :=
  [rPmul1, rPmulO, rPmulI, rNmul0l, rNmul0r, rNmulPp, rNdivmod, rNmod64]

def arithmeticRules : List FORule :=
  psuccRules ++ paddRules ++ paddcRules ++ naddRules ++ orderRules ++ wordRules ++ mulRules

/-! ## Lists -/

def rLenNil : FORule :=
  mkRule "vibe-len-nil" [] [] (jLen cNil cN0)

def rLenCons : FORule :=
  mkRule "vibe-len-cons" ["x", "xs", "n", "k"]
    [jLen (mv "xs") (mv "n"), jNAdd (mv "n") patOne (mv "k")]
    (jLen (cCons (mv "x") (mv "xs")) (mv "k"))

def rNth0 : FORule :=
  mkRule "vibe-nth-0" ["x", "xs"] [] (jNth (cCons (mv "x") (mv "xs")) cN0 (mv "x"))

def rNthS : FORule :=
  mkRule "vibe-nth-s" ["x", "xs", "i", "j", "y"]
    [jNAdd (mv "j") patOne (mv "i"), jNth (mv "xs") (mv "j") (mv "y")]
    (jNth (cCons (mv "x") (mv "xs")) (mv "i") (mv "y"))

def rBytesNil : FORule :=
  mkRule "vibe-bytes-nil" [] [] (jBytes cNil)

def rBytesCons : FORule :=
  mkRule "vibe-bytes-cons" ["x", "xs"] [jNLt (mv "x") patByteBound, jBytes (mv "xs")]
    (jBytes (cCons (mv "x") (mv "xs")))

def listRules : List FORule :=
  [rLenNil, rLenCons, rNth0, rNthS, rBytesNil, rBytesCons]

/-! ## Term formation and annotations -/

def rWfBvar : FORule :=
  mkRule "vibe-wf-bvar" ["n", "k"]
    [jNAdd (mv "n") patOne (mv "k"), jNWord (mv "k")] (jWf (cBVar (mv "n")))

def rWfLit : FORule :=
  mkRule "vibe-wf-lit" ["bs", "len", "k"]
    [jBytes (mv "bs"), jLen (mv "bs") (mv "len"), jNAdd (mv "len") patEight (mv "k"),
      jNWord (mv "k")]
    (jWf (cLit (mv "bs")))

def rWfApp : FORule :=
  mkRule "vibe-wf-app" ["id", "kind", "bs", "ts", "d", "f", "g"]
    [jSymDecl (cSym (mv "id") (mv "kind") (mv "bs")),
      jWfArgs (mv "bs") (mv "ts") (mv "d") (mv "f"), jKindFv (mv "kind") (mv "f") (mv "g")]
    (jWf (cApp (cSym (mv "id") (mv "kind") (mv "bs")) (mv "ts") (cAnn (mv "d") (mv "g"))))

def rWfargsNil : FORule :=
  mkRule "vibe-wfargs-nil" [] [] (jWfArgs cNil cNil cN0 cFalse)

def rWfargsCons : FORule :=
  mkRule "vibe-wfargs-cons" ["b", "bs", "t", "ts", "dt", "e", "dr", "fr", "ft", "d", "f"]
    [jWf (mv "t"), jDepth (mv "t") (mv "dt"), jNMonus (mv "dt") (mv "b") (mv "e"),
      jHasFv (mv "t") (mv "ft"), jWfArgs (mv "bs") (mv "ts") (mv "dr") (mv "fr"),
      jNMax (mv "e") (mv "dr") (mv "d"), jBOr (mv "ft") (mv "fr") (mv "f")]
    (jWfArgs (cCons (mv "b") (mv "bs")) (cCons (mv "t") (mv "ts")) (mv "d") (mv "f"))

def rKindfvConst : FORule :=
  mkRule "vibe-kindfv-const" ["f"] [] (jKindFv cKConst (mv "f") (mv "f"))

def rKindfvFvar : FORule :=
  mkRule "vibe-kindfv-fvar" ["f"] [] (jKindFv cKFvar (mv "f") cTrue)

def rDepthBvar : FORule :=
  mkRule "vibe-depth-bvar" ["n", "d"] [jNAdd (mv "n") patOne (mv "d")]
    (jDepth (cBVar (mv "n")) (mv "d"))

def rDepthLit : FORule :=
  mkRule "vibe-depth-lit" ["bs"] [] (jDepth (cLit (mv "bs")) cN0)

def rDepthApp : FORule :=
  mkRule "vibe-depth-app" ["s", "ts", "d", "f"] []
    (jDepth (cApp (mv "s") (mv "ts") (cAnn (mv "d") (mv "f"))) (mv "d"))

def rHasfvBvar : FORule :=
  mkRule "vibe-hasfv-bvar" ["n"] [] (jHasFv (cBVar (mv "n")) cFalse)

def rHasfvLit : FORule :=
  mkRule "vibe-hasfv-lit" ["bs"] [] (jHasFv (cLit (mv "bs")) cFalse)

def rHasfvApp : FORule :=
  mkRule "vibe-hasfv-app" ["s", "ts", "d", "f"] []
    (jHasFv (cApp (mv "s") (mv "ts") (cAnn (mv "d") (mv "f"))) (mv "f"))

def rAnnargsNil : FORule :=
  mkRule "vibe-annargs-nil" [] [] (jAnnArgs cNil cNil cN0 cFalse)

def rAnnargsCons : FORule :=
  mkRule "vibe-annargs-cons" ["b", "bs", "t", "ts", "dt", "e", "dr", "fr", "ft", "d", "f"]
    [jDepth (mv "t") (mv "dt"), jNMonus (mv "dt") (mv "b") (mv "e"),
      jHasFv (mv "t") (mv "ft"), jAnnArgs (mv "bs") (mv "ts") (mv "dr") (mv "fr"),
      jNMax (mv "e") (mv "dr") (mv "d"), jBOr (mv "ft") (mv "fr") (mv "f")]
    (jAnnArgs (cCons (mv "b") (mv "bs")) (cCons (mv "t") (mv "ts")) (mv "d") (mv "f"))

def termRules : List FORule :=
  [rWfBvar, rWfLit, rWfApp, rWfargsNil, rWfargsCons, rKindfvConst, rKindfvFvar, rDepthBvar, rDepthLit, rDepthApp, rHasfvBvar, rHasfvLit, rHasfvApp, rAnnargsNil, rAnnargsCons]

/-! ## Shifting -/

def rShiftZero : FORule :=
  mkRule "vibe-shift-zero" ["c", "t"] [] (jShift cN0 (mv "c") (mv "t") (mv "t"))

def rShiftLow : FORule :=
  mkRule "vibe-shift-low" ["a", "c", "t", "d"]
    [jDepth (mv "t") (mv "d"), jNLe (mv "d") (mv "c")] (jShift (mv "a") (mv "c") (mv "t") (mv "t"))

def rShiftBvar : FORule :=
  mkRule "vibe-shift-bvar" ["p", "c", "b", "r"]
    [jNLe (mv "c") (mv "b"), jNAdd (mv "b") (cNPos (mv "p")) (mv "r"), jNLt (mv "r") patMaxWord]
    (jShift (cNPos (mv "p")) (mv "c") (cBVar (mv "b")) (cBVar (mv "r")))

def rShiftApp : FORule :=
  mkRule "vibe-shift-app"
    ["p", "c", "id", "kind", "bs", "ts", "d", "f", "us", "e", "g", "h"]
    [jNLt (mv "c") (mv "d"),
      jShiftArgs (cNPos (mv "p")) (mv "c") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g"), jKindFv (mv "kind") (mv "g") (mv "h")]
    (jShift (cNPos (mv "p")) (mv "c")
      (cApp (cSym (mv "id") (mv "kind") (mv "bs")) (mv "ts") (cAnn (mv "d") (mv "f")))
      (cApp (cSym (mv "id") (mv "kind") (mv "bs")) (mv "us") (cAnn (mv "e") (mv "h"))))

def rShiftargsNil : FORule :=
  mkRule "vibe-shiftargs-nil" ["a", "c"] [] (jShiftArgs (mv "a") (mv "c") cNil cNil cNil)

def rShiftargsCons : FORule :=
  mkRule "vibe-shiftargs-cons" ["a", "c", "b", "bs", "t", "ts", "u", "us", "k"]
    [jNAdd (mv "c") (mv "b") (mv "k"), jNWord (mv "k"), jShift (mv "a") (mv "k") (mv "t") (mv "u"),
      jShiftArgs (mv "a") (mv "c") (mv "bs") (mv "ts") (mv "us")]
    (jShiftArgs (mv "a") (mv "c") (cCons (mv "b") (mv "bs")) (cCons (mv "t") (mv "ts"))
      (cCons (mv "u") (mv "us")))

def shiftRules : List FORule :=
  [rShiftZero, rShiftLow, rShiftBvar, rShiftApp, rShiftargsNil, rShiftargsCons]

/-! ## Plugging arguments for bound variables -/

def rSubstLow : FORule :=
  mkRule "vibe-subst-low" ["n", "args", "o", "t", "d"]
    [jDepth (mv "t") (mv "d"), jNLe (mv "d") (mv "o")]
    (jSubst (mv "n") (mv "args") (mv "o") (mv "t") (mv "t"))

def rSubstParam : FORule :=
  mkRule "vibe-subst-param" ["n", "args", "o", "b", "k", "k1", "i", "a", "r"]
    [jNAdd (mv "o") (mv "k") (mv "b"), jNLt (mv "k") (mv "n"), jNAdd (mv "k") patOne (mv "k1"),
      jNAdd (mv "i") (mv "k1") (mv "n"), jNth (mv "args") (mv "i") (mv "a"),
      jShift (mv "o") cN0 (mv "a") (mv "r")]
    (jSubst (mv "n") (mv "args") (mv "o") (cBVar (mv "b")) (mv "r"))

def rSubstAbove : FORule :=
  mkRule "vibe-subst-above" ["n", "args", "o", "b", "k", "k1"]
    [jNAdd (mv "o") (mv "k") (mv "b"), jNLe (mv "n") (mv "k"),
      jNAdd (mv "k") patOne (mv "k1"), jNWord (mv "k1")]
    (jSubst (mv "n") (mv "args") (mv "o") (cBVar (mv "b")) (cBVar (mv "k")))

def rSubstApp : FORule :=
  mkRule "vibe-subst-app"
    ["n", "args", "o", "id", "kind", "bs", "ts", "d", "f", "us", "e", "g", "h"]
    [jNLt (mv "o") (mv "d"),
      jSubstArgs (mv "n") (mv "args") (mv "o") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g"), jKindFv (mv "kind") (mv "g") (mv "h")]
    (jSubst (mv "n") (mv "args") (mv "o")
      (cApp (cSym (mv "id") (mv "kind") (mv "bs")) (mv "ts") (cAnn (mv "d") (mv "f")))
      (cApp (cSym (mv "id") (mv "kind") (mv "bs")) (mv "us") (cAnn (mv "e") (mv "h"))))

def rSubstargsNil : FORule :=
  mkRule "vibe-substargs-nil" ["n", "args", "o"] []
    (jSubstArgs (mv "n") (mv "args") (mv "o") cNil cNil cNil)

def rSubstargsCons : FORule :=
  mkRule "vibe-substargs-cons" ["n", "args", "o", "b", "bs", "t", "ts", "u", "us", "k"]
    [jNAdd (mv "o") (mv "b") (mv "k"), jNWord (mv "k"),
      jSubst (mv "n") (mv "args") (mv "k") (mv "t") (mv "u"),
      jSubstArgs (mv "n") (mv "args") (mv "o") (mv "bs") (mv "ts") (mv "us")]
    (jSubstArgs (mv "n") (mv "args") (mv "o") (cCons (mv "b") (mv "bs"))
      (cCons (mv "t") (mv "ts")) (cCons (mv "u") (mv "us")))

def rSubsttop0 : FORule :=
  mkRule "vibe-substtop-0" ["args", "t"] [] (jSubstTop cN0 (mv "args") (mv "t") (mv "t"))

def rSubsttopP : FORule :=
  mkRule "vibe-substtop-p" ["p", "args", "t", "r"]
    [jSubst (cNPos (mv "p")) (mv "args") cN0 (mv "t") (mv "r")]
    (jSubstTop (cNPos (mv "p")) (mv "args") (mv "t") (mv "r"))

def substRules : List FORule :=
  [rSubstLow, rSubstParam, rSubstAbove, rSubstApp, rSubstargsNil, rSubstargsCons, rSubsttop0, rSubsttopP]

/-! ## Instantiating a free variable -/

def fvarSym : Pattern := cSym (mv "fid") cKFvar (mv "fbs")

def rInstNofv : FORule :=
  mkRule "vibe-inst-nofv" ["F", "v", "n", "o", "t"] [jHasFv (mv "t") cFalse]
    (jInst (mv "F") (mv "v") (mv "n") (mv "o") (mv "t") (mv "t"))

def rInstConst : FORule :=
  mkRule "vibe-inst-const"
    ["F", "v", "n", "o", "id", "bs", "ts", "d", "us", "e", "g"]
    [jInstArgs (mv "F") (mv "v") (mv "n") (mv "o") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g")]
    (jInst (mv "F") (mv "v") (mv "n") (mv "o")
      (cApp (cSym (mv "id") cKConst (mv "bs")) (mv "ts") (cAnn (mv "d") cTrue))
      (cApp (cSym (mv "id") cKConst (mv "bs")) (mv "us") (cAnn (mv "e") (mv "g"))))

def rInstOtherLt : FORule :=
  mkRule "vibe-inst-other-lt"
    ["fid", "fbs", "v", "n", "o", "id", "bs", "ts", "d", "us", "e", "g"]
    [jNLt (mv "id") (mv "fid"),
      jInstArgs fvarSym (mv "v") (mv "n") (mv "o") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g")]
    (jInst fvarSym (mv "v") (mv "n") (mv "o")
      (cApp (cSym (mv "id") cKFvar (mv "bs")) (mv "ts") (cAnn (mv "d") cTrue))
      (cApp (cSym (mv "id") cKFvar (mv "bs")) (mv "us") (cAnn (mv "e") cTrue)))

def rInstOtherGt : FORule :=
  mkRule "vibe-inst-other-gt"
    ["fid", "fbs", "v", "n", "o", "id", "bs", "ts", "d", "us", "e", "g"]
    [jNLt (mv "fid") (mv "id"),
      jInstArgs fvarSym (mv "v") (mv "n") (mv "o") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g")]
    (jInst fvarSym (mv "v") (mv "n") (mv "o")
      (cApp (cSym (mv "id") cKFvar (mv "bs")) (mv "ts") (cAnn (mv "d") cTrue))
      (cApp (cSym (mv "id") cKFvar (mv "bs")) (mv "us") (cAnn (mv "e") cTrue)))

def rInstHit : FORule :=
  mkRule "vibe-inst-hit" ["fid", "fbs", "v", "n", "o", "ts", "d", "us", "w", "r"]
    [jInstArgs fvarSym (mv "v") (mv "n") (mv "o") (mv "fbs") (mv "ts") (mv "us"),
      jShift (mv "o") (mv "n") (mv "v") (mv "w"), jSubstTop (mv "n") (mv "us") (mv "w") (mv "r")]
    (jInst fvarSym (mv "v") (mv "n") (mv "o") (cApp fvarSym (mv "ts") (cAnn (mv "d") cTrue))
      (mv "r"))

def rInstargsNil : FORule :=
  mkRule "vibe-instargs-nil" ["F", "v", "n", "o"] []
    (jInstArgs (mv "F") (mv "v") (mv "n") (mv "o") cNil cNil cNil)

def rInstargsCons : FORule :=
  mkRule "vibe-instargs-cons" ["F", "v", "n", "o", "b", "bs", "t", "ts", "u", "us", "k"]
    [jNAdd (mv "o") (mv "b") (mv "k"), jNWord (mv "k"),
      jInst (mv "F") (mv "v") (mv "n") (mv "k") (mv "t") (mv "u"),
      jInstArgs (mv "F") (mv "v") (mv "n") (mv "o") (mv "bs") (mv "ts") (mv "us")]
    (jInstArgs (mv "F") (mv "v") (mv "n") (mv "o") (cCons (mv "b") (mv "bs"))
      (cCons (mv "t") (mv "ts")) (cCons (mv "u") (mv "us")))

def instRules : List FORule :=
  [rInstNofv, rInstConst, rInstOtherLt, rInstOtherGt, rInstHit, rInstargsNil, rInstargsCons]

/-! ## Number literals -/

def byteList8 : Pattern :=
  cCons (mv "r1") (cCons (mv "r2") (cCons (mv "r3") (cCons (mv "r4")
    (cCons (mv "r5") (cCons (mv "r6") (cCons (mv "r7") (cCons (mv "r8") cNil)))))))

def rNatlitSmall : FORule :=
  mkRule "vibe-natlit-small" ["n", "p"] [jNAdd (mv "n") (cNPos (mv "p")) patByteBound]
    (jNatLit (mv "n") (cCons (mv "n") cNil))

def rNatlitLarge : FORule :=
  mkRule "vibe-natlit-large"
    ["n", "q1", "q2", "q3", "q4", "q5", "q6", "q7", "q8",
      "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8"]
    [jNLe patByteBound (mv "n"),
      jNDivMod (mv "n") patByteBound (mv "q1") (mv "r1"),
      jNDivMod (mv "q1") patByteBound (mv "q2") (mv "r2"),
      jNDivMod (mv "q2") patByteBound (mv "q3") (mv "r3"),
      jNDivMod (mv "q3") patByteBound (mv "q4") (mv "r4"),
      jNDivMod (mv "q4") patByteBound (mv "q5") (mv "r5"),
      jNDivMod (mv "q5") patByteBound (mv "q6") (mv "r6"),
      jNDivMod (mv "q6") patByteBound (mv "q7") (mv "r7"),
      jNDivMod (mv "q7") patByteBound (mv "q8") (mv "r8")]
    (jNatLit (mv "n") byteList8)

def literalRules : List FORule :=
  [rNatlitSmall, rNatlitLarge]

/-! ## Theorems -/

def patImpl : Pattern := patBuiltinSym .impl
def patEq : Pattern := patBuiltinSym .eq

/-- A closed binary application of a built-in constant. -/
def closedApp2 (head x y : Pattern) : Pattern :=
  cApp head (cCons x (cCons y cNil)) patAnnClosed

def closedApp1 (head x : Pattern) : Pattern :=
  cApp head (cCons x cNil) patAnnClosed

def rMp : FORule :=
  mkRule "vibe-mp" ["a", "b", "ann"]
    [jThm (cApp patImpl (cCons (mv "a") (cCons (mv "b") cNil)) (mv "ann")), jThm (mv "a")]
    (jThm (mv "b"))

def rInst : FORule :=
  mkRule "vibe-inst" ["phi", "fid", "fbs", "n", "v", "dv", "psi"]
    [jThm (mv "phi"), jSymDecl fvarSym, jLen (mv "fbs") (mv "n"), jWf (mv "v"),
      jDepth (mv "v") (mv "dv"), jNLe (mv "dv") (mv "n"),
      jInst fvarSym (mv "v") (mv "n") cN0 (mv "phi") (mv "psi"), jDepth (mv "psi") cN0]
    (jThm (mv "psi"))

def rLitIsnat : FORule :=
  mkRule "vibe-lit-isnat" ["n", "bn"] [jNWord (mv "n"), jNatLit (mv "n") (mv "bn")]
    (jThm (closedApp1 (patBuiltinSym .litIsNat) (cLit (mv "bn"))))

def rLitLt : FORule :=
  mkRule "vibe-lit-lt" ["a", "b", "ba", "bb"]
    [jNLt (mv "a") (mv "b"), jNWord (mv "b"), jNatLit (mv "a") (mv "ba"),
      jNatLit (mv "b") (mv "bb")]
    (jThm (closedApp2 (patBuiltinSym .litLt) (cLit (mv "ba")) (cLit (mv "bb"))))

def rLitAdd : FORule :=
  mkRule "vibe-lit-add" ["a", "b", "s", "c", "ba", "bb", "bc"]
    [jNWord (mv "a"), jNWord (mv "b"), jNAdd (mv "a") (mv "b") (mv "s"),
      jNMod64 (mv "s") (mv "c"), jNatLit (mv "a") (mv "ba"), jNatLit (mv "b") (mv "bb"),
      jNatLit (mv "c") (mv "bc")]
    (jThm (closedApp2 patEq
      (closedApp2 (patBuiltinSym .litAdd) (cLit (mv "ba")) (cLit (mv "bb")))
      (cLit (mv "bc"))))

def rLitMul : FORule :=
  mkRule "vibe-lit-mul" ["a", "b", "s", "c", "ba", "bb", "bc"]
    [jNWord (mv "a"), jNWord (mv "b"), jNMul (mv "a") (mv "b") (mv "s"),
      jNMod64 (mv "s") (mv "c"), jNatLit (mv "a") (mv "ba"), jNatLit (mv "b") (mv "bb"),
      jNatLit (mv "c") (mv "bc")]
    (jThm (closedApp2 patEq
      (closedApp2 (patBuiltinSym .litMul) (cLit (mv "ba")) (cLit (mv "bb")))
      (cLit (mv "bc"))))

def rLitDiv : FORule :=
  mkRule "vibe-lit-div" ["a", "b", "q", "r", "ba", "bb", "bq"]
    [jNWord (mv "a"), jNWord (mv "b"), jNDivMod (mv "a") (mv "b") (mv "q") (mv "r"),
      jNatLit (mv "a") (mv "ba"), jNatLit (mv "b") (mv "bb"), jNatLit (mv "q") (mv "bq")]
    (jThm (closedApp2 patEq
      (closedApp2 (patBuiltinSym .litDiv) (cLit (mv "ba")) (cLit (mv "bb")))
      (cLit (mv "bq"))))

def rLitLength : FORule :=
  mkRule "vibe-lit-length" ["bs", "n", "bn"]
    [jWf (cLit (mv "bs")), jLen (mv "bs") (mv "n"), jNatLit (mv "n") (mv "bn")]
    (jThm (closedApp2 patEq (closedApp1 (patBuiltinSym .litLength) (cLit (mv "bs")))
      (cLit (mv "bn"))))

def rLitGet : FORule :=
  mkRule "vibe-lit-get" ["bs", "i", "x", "bi", "bx"]
    [jWf (cLit (mv "bs")), jNth (mv "bs") (mv "i") (mv "x"), jNatLit (mv "i") (mv "bi"),
      jNatLit (mv "x") (mv "bx")]
    (jThm (closedApp2 patEq
      (closedApp2 (patBuiltinSym .litGet) (cLit (mv "bs")) (cLit (mv "bi")))
      (cLit (mv "bx"))))

def theoremRules : List FORule :=
  [rMp, rInst, rLitIsnat, rLitLt, rLitAdd, rLitMul, rLitDiv, rLitLength, rLitGet]

/-! ## Definitions -/

def rAritiesNil : FORule :=
  mkRule "vibe-arities-nil" [] [] (jArities cNil cNil)

def rAritiesCons : FORule :=
  mkRule "vibe-arities-cons" ["id", "fbs", "fvars", "n", "bs"]
    [jSymDecl (cSym (mv "id") cKFvar (mv "fbs")), jLen (mv "fbs") (mv "n"),
      jArities (mv "fvars") (mv "bs")]
    (jArities (cCons (cSym (mv "id") cKFvar (mv "fbs")) (mv "fvars")) (cCons (mv "n") (mv "bs")))

def rHintsinNil : FORule :=
  mkRule "vibe-hintsin-nil" ["n"] [] (jHintsIn cNil (mv "n"))

def rHintsinCons : FORule :=
  mkRule "vibe-hintsin-cons" ["h", "hs", "n"] [jNLt (mv "h") (mv "n"), jHintsIn (mv "hs") (mv "n")]
    (jHintsIn (cCons (mv "h") (mv "hs")) (mv "n"))

def rOccBvar : FORule :=
  mkRule "vibe-occ-bvar" ["fvars", "i", "hs"] [] (jOcc (mv "fvars") (cBVar (mv "i")) (mv "hs") (mv "hs"))

def rOccLit : FORule :=
  mkRule "vibe-occ-lit" ["fvars", "bs", "hs"] [] (jOcc (mv "fvars") (cLit (mv "bs")) (mv "hs") (mv "hs"))

def rOccConst : FORule :=
  mkRule "vibe-occ-const" ["fvars", "id", "bs", "ts", "ann", "hs", "rest"]
    [jOccArgs (mv "fvars") (mv "ts") (mv "hs") (mv "rest")]
    (jOcc (mv "fvars") (cApp (cSym (mv "id") cKConst (mv "bs")) (mv "ts") (mv "ann"))
      (mv "hs") (mv "rest"))

def rOccFvar : FORule :=
  mkRule "vibe-occ-fvar" ["fvars", "id", "bs", "ts", "ann", "h", "hs", "rest"]
    [jNth (mv "fvars") (mv "h") (cSym (mv "id") cKFvar (mv "bs")),
      jOccArgs (mv "fvars") (mv "ts") (mv "hs") (mv "rest")]
    (jOcc (mv "fvars") (cApp (cSym (mv "id") cKFvar (mv "bs")) (mv "ts") (mv "ann"))
      (cCons (mv "h") (mv "hs")) (mv "rest"))

def rOccargsNil : FORule :=
  mkRule "vibe-occargs-nil" ["fvars", "hs"] [] (jOccArgs (mv "fvars") cNil (mv "hs") (mv "hs"))

def rOccargsCons : FORule :=
  mkRule "vibe-occargs-cons" ["fvars", "t", "ts", "hs", "mid", "rest"]
    [jOcc (mv "fvars") (mv "t") (mv "hs") (mv "mid"),
      jOccArgs (mv "fvars") (mv "ts") (mv "mid") (mv "rest")]
    (jOccArgs (mv "fvars") (cCons (mv "t") (mv "ts")) (mv "hs") (mv "rest"))

def rDesc0 : FORule :=
  mkRule "vibe-desc-0" [] [] (jDescBVars cN0 cNil)

def rDescS : FORule :=
  mkRule "vibe-desc-s" ["n", "k", "vars"]
    [jNAdd (mv "k") patOne (mv "n"), jDescBVars (mv "k") (mv "vars")]
    (jDescBVars (mv "n") (cCons (cBVar (mv "k")) (mv "vars")))

def rEtasNil : FORule :=
  mkRule "vibe-etas-nil" [] [] (jEtas cNil cNil)

def rEtasCons : FORule :=
  mkRule "vibe-etas-cons" ["id", "fbs", "fvars", "n", "vars", "etas"]
    [jLen (mv "fbs") (mv "n"), jDescBVars (mv "n") (mv "vars"), jEtas (mv "fvars") (mv "etas")]
    (jEtas (cCons (cSym (mv "id") cKFvar (mv "fbs")) (mv "fvars"))
      (cCons (cApp (cSym (mv "id") cKFvar (mv "fbs")) (mv "vars") (cAnn (mv "n") cTrue))
        (mv "etas")))

def rDefstmt : FORule :=
  mkRule "vibe-defstmt"
    ["cid", "fvars", "bs", "n", "hints", "value", "rest", "etas", "dl", "fl",
      "de", "fe"]
    [jArities (mv "fvars") (mv "bs"), jLen (mv "fvars") (mv "n"), jHintsIn (mv "hints") (mv "n"),
      jWf (mv "value"), jDepth (mv "value") cN0,
      jOcc (mv "fvars") (mv "value") (mv "hints") (mv "rest"),
      jEtas (mv "fvars") (mv "etas"), jAnnArgs (mv "bs") (mv "etas") (mv "dl") (mv "fl"),
      jAnnArgs (cCons cN0 (cCons cN0 cNil))
        (cCons (cApp (cSym (mv "cid") cKConst (mv "bs")) (mv "etas") (cAnn (mv "dl") (mv "fl")))
          (cCons (mv "value") cNil)) (mv "de") (mv "fe")]
    (jDefStmt (cSym (mv "cid") cKConst (mv "bs")) (mv "fvars") (mv "hints") (mv "value")
      (cApp patEq
        (cCons (cApp (cSym (mv "cid") cKConst (mv "bs")) (mv "etas") (cAnn (mv "dl") (mv "fl")))
          (cCons (mv "value") cNil))
        (cAnn (mv "de") (mv "fe"))))

def definitionRules : List FORule :=
  [rAritiesNil, rAritiesCons, rHintsinNil, rHintsinCons, rOccBvar, rOccLit, rOccConst, rOccFvar, rOccargsNil, rOccargsCons, rDesc0, rDescS, rEtasNil, rEtasCons, rDefstmt]

/-! ## Built-in symbols -/

def builtinRules : List FORule :=
  Builtin.all.map fun b =>
    mkRule ("vibe-builtin-" ++ toString b.slot) [] [] (jSymDecl (patBuiltinSym b))

/-- The fixed kernel package. -/
def kernelRules : List FORule :=
  arithmeticRules ++ listRules ++ termRules ++ shiftRules ++ substRules ++ instRules ++
    literalRules ++ theoremRules ++ definitionRules ++ builtinRules

end Mettapedia.Languages.VibeITP.Presentation
