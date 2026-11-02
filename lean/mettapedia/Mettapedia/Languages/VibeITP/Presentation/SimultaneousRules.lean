import Mettapedia.Languages.VibeITP.Presentation.Validation

/-!
# Additive rule schemas for simultaneous instantiation

Pairs and prepared entries use the existing list constructors. The new
judgments retain validation, first-match hit/miss evidence, original-child
traversal and final closure. The empty environment has its own copying rule.
Structural validation of this package is separate from semantic soundness.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection

def pairPattern (symbol value : Pattern) : Pattern := cCons symbol (cCons value cNil)
def entryPattern (symbol arity value : Pattern) : Pattern :=
  cCons symbol (cCons arity (cCons value cNil))

def jManyPrepare (replacements entries : Pattern) : Pattern :=
  .apply "VManyPrepare" [replacements, entries]
def jManyHit (entries symbol arity value : Pattern) : Pattern :=
  .apply "VManyHit" [entries, symbol, arity, value]
def jManyMiss (entries symbol : Pattern) : Pattern := .apply "VManyMiss" [entries, symbol]
def jMany (entries offset source result : Pattern) : Pattern :=
  .apply "VMany" [entries, offset, source, result]
def jManyArgs (entries offset binders arguments results : Pattern) : Pattern :=
  .apply "VManyArgs" [entries, offset, binders, arguments, results]

def simultaneousJudgments : List JudgmentDecl :=
  [⟨"VManyPrepare", 2⟩, ⟨"VManyHit", 4⟩, ⟨"VManyMiss", 2⟩,
    ⟨"VMany", 4⟩, ⟨"VManyArgs", 5⟩]

def rManyPrepareNil : FORule :=
  mkRule "vibe-many-prepare-nil" [] [] (jManyPrepare cNil cNil)

def rManyPrepareCons : FORule :=
  mkRule "vibe-many-prepare-cons" ["fid", "fbs", "v", "n", "d", "reps", "entries"]
    [jSymDecl fvarSym, jLen (mv "fbs") (mv "n"), jWf (mv "v"),
      jDepth (mv "v") (mv "d"), jNLe (mv "d") (mv "n"),
      jManyPrepare (mv "reps") (mv "entries")]
    (jManyPrepare (cCons (pairPattern fvarSym (mv "v")) (mv "reps"))
      (cCons (entryPattern fvarSym (mv "n") (mv "v")) (mv "entries")))

def rManyHitFirst : FORule :=
  mkRule "vibe-many-hit-first" ["fid", "fbs", "n", "v", "rest"] []
    (jManyHit (cCons (entryPattern fvarSym (mv "n") (mv "v")) (mv "rest"))
      fvarSym (mv "n") (mv "v"))

def rManyHitLt : FORule :=
  mkRule "vibe-many-hit-lt" ["id", "bs", "k", "w", "rest", "fid", "fbs", "n", "v"]
    [jNLt (mv "id") (mv "fid"), jManyHit (mv "rest") fvarSym (mv "n") (mv "v")]
    (jManyHit (cCons (entryPattern (cSym (mv "id") cKFvar (mv "bs")) (mv "k") (mv "w")) (mv "rest"))
      fvarSym (mv "n") (mv "v"))

def rManyHitGt : FORule :=
  mkRule "vibe-many-hit-gt" ["id", "bs", "k", "w", "rest", "fid", "fbs", "n", "v"]
    [jNLt (mv "fid") (mv "id"), jManyHit (mv "rest") fvarSym (mv "n") (mv "v")]
    (jManyHit (cCons (entryPattern (cSym (mv "id") cKFvar (mv "bs")) (mv "k") (mv "w")) (mv "rest"))
      fvarSym (mv "n") (mv "v"))

def rManyMissNil : FORule :=
  mkRule "vibe-many-miss-nil" ["fid", "fbs"] [] (jManyMiss cNil fvarSym)

def rManyMissLt : FORule :=
  mkRule "vibe-many-miss-lt" ["id", "bs", "k", "w", "rest", "fid", "fbs"]
    [jNLt (mv "id") (mv "fid"), jManyMiss (mv "rest") fvarSym]
    (jManyMiss (cCons (entryPattern (cSym (mv "id") cKFvar (mv "bs")) (mv "k") (mv "w")) (mv "rest")) fvarSym)

def rManyMissGt : FORule :=
  mkRule "vibe-many-miss-gt" ["id", "bs", "k", "w", "rest", "fid", "fbs"]
    [jNLt (mv "fid") (mv "id"), jManyMiss (mv "rest") fvarSym]
    (jManyMiss (cCons (entryPattern (cSym (mv "id") cKFvar (mv "bs")) (mv "k") (mv "w")) (mv "rest")) fvarSym)

def rManyNofv : FORule :=
  mkRule "vibe-many-nofv" ["entries", "o", "t"] [jHasFv (mv "t") cFalse]
    (jMany (mv "entries") (mv "o") (mv "t") (mv "t"))

def rManyConst : FORule :=
  mkRule "vibe-many-const" ["entries", "o", "id", "bs", "ts", "d", "us", "e", "g"]
    [jManyArgs (mv "entries") (mv "o") (mv "bs") (mv "ts") (mv "us"),
      jAnnArgs (mv "bs") (mv "us") (mv "e") (mv "g")]
    (jMany (mv "entries") (mv "o")
      (cApp (cSym (mv "id") cKConst (mv "bs")) (mv "ts") (cAnn (mv "d") cTrue))
      (cApp (cSym (mv "id") cKConst (mv "bs")) (mv "us") (cAnn (mv "e") (mv "g"))))

def rManyAbsent : FORule :=
  mkRule "vibe-many-absent" ["entries", "o", "fid", "fbs", "ts", "d", "us", "e", "g"]
    [jManyMiss (mv "entries") fvarSym,
      jManyArgs (mv "entries") (mv "o") (mv "fbs") (mv "ts") (mv "us"),
      jAnnArgs (mv "fbs") (mv "us") (mv "e") (mv "g")]
    (jMany (mv "entries") (mv "o") (cApp fvarSym (mv "ts") (cAnn (mv "d") cTrue))
      (cApp fvarSym (mv "us") (cAnn (mv "e") cTrue)))

def rManySelected : FORule :=
  mkRule "vibe-many-selected" ["entries", "o", "fid", "fbs", "n", "v", "ts", "d", "us", "w", "r"]
    [jManyHit (mv "entries") fvarSym (mv "n") (mv "v"),
      jManyArgs (mv "entries") (mv "o") (mv "fbs") (mv "ts") (mv "us"),
      jShift (mv "o") (mv "n") (mv "v") (mv "w"),
      jSubstTop (mv "n") (mv "us") (mv "w") (mv "r")]
    (jMany (mv "entries") (mv "o") (cApp fvarSym (mv "ts") (cAnn (mv "d") cTrue)) (mv "r"))

def rManyArgsNil : FORule :=
  mkRule "vibe-many-args-nil" ["entries", "o"] []
    (jManyArgs (mv "entries") (mv "o") cNil cNil cNil)

def rManyArgsCons : FORule :=
  mkRule "vibe-many-args-cons" ["entries", "o", "b", "bs", "t", "ts", "u", "us", "k"]
    [jNAdd (mv "o") (mv "b") (mv "k"), jNWord (mv "k"),
      jMany (mv "entries") (mv "k") (mv "t") (mv "u"),
      jManyArgs (mv "entries") (mv "o") (mv "bs") (mv "ts") (mv "us")]
    (jManyArgs (mv "entries") (mv "o") (cCons (mv "b") (mv "bs"))
      (cCons (mv "t") (mv "ts")) (cCons (mv "u") (mv "us")))

def rInstantiateManyNil : FORule :=
  mkRule "vibe-thm-many-nil" ["phi"] [jThm (mv "phi"), jDepth (mv "phi") cN0] (jThm (mv "phi"))

def rInstantiateManyCons : FORule :=
  mkRule "vibe-thm-many-cons" ["rep", "reps", "entry", "entries", "phi", "psi"]
    [jThm (mv "phi"),
      jManyPrepare (cCons (mv "rep") (mv "reps")) (cCons (mv "entry") (mv "entries")),
      jMany (cCons (mv "entry") (mv "entries")) cN0 (mv "phi") (mv "psi"),
      jDepth (mv "psi") cN0]
    (jThm (mv "psi"))

def simultaneousRules : List FORule :=
  [rManyPrepareNil, rManyPrepareCons, rManyHitFirst, rManyHitLt, rManyHitGt,
    rManyMissNil, rManyMissLt, rManyMissGt, rManyNofv, rManyConst,
    rManyAbsent, rManySelected, rManyArgsNil, rManyArgsCons, rInstantiateManyNil, rInstantiateManyCons]

def rulesV2 : List FORule := kernelRules ++ simultaneousRules

def fixedDefinitionV2 : CalculusLanguageDef :=
  cacheDefinition { kernelProfile with cacheName := "vibe-itp-kernel-v2" }
    constructorArities (kernelJudgments ++ simultaneousJudgments) (rulesV2.map FORule.toSchema)

set_option maxRecDepth 100000 in
theorem fixedDefinitionV2_valid : fixedDefinitionV2.isValid = true := by decide +kernel

theorem simultaneousRules_foPackage : FOPackage simultaneousRules := by
  have names : simultaneousRules.all (fun rule => decide rule.vars.Nodup) = true := by decide +kernel
  have premises : simultaneousRules.all
      (fun rule => checkBindingSchemasFragment rule.formals rule.premises) = true := by decide +kernel
  have conclusions : simultaneousRules.all
      (fun rule => checkBindingSchemaFragment rule.formals rule.conclusion) = true := by decide +kernel
  exact ⟨fun rule member => of_decide_eq_true (List.all_eq_true.mp names rule member),
    fun rule member => bindingSchemasFragment_of_check (List.all_eq_true.mp premises rule member),
    fun rule member => bindingSchemaFragment_of_check (List.all_eq_true.mp conclusions rule member)⟩

theorem rulesV2_foPackage : FOPackage rulesV2 := kernelRules_foPackage.append simultaneousRules_foPackage

def fixedValidatedV2 : ValidatedCalculusLanguageDef := ⟨fixedDefinitionV2, fixedDefinitionV2_valid⟩

theorem fixedValidatedV2_presents : Presents fixedValidatedV2 rulesV2 := ⟨rulesV2_foPackage, rfl⟩

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
