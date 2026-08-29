import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RussellTarskiBoundary
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralLaws

/-!
# Schema binders elaborate to lexical dependent products

This module makes the universe-polymorphic functional-composition schema
explicit.  Universe
parameters remain parameters of the admitted level algebra; type parameters
become ordinary lexical binders whose domains are the corresponding universe
sorts.  Matcher variables play no role in this translation.

The target is the independent cumulative `Tower` judgment.  This is
intentional: the code presentation proved in `RussellTarskiBoundary` currently
covers generated codes but not first-class neutral code variables.  Therefore
the present theorem licenses the Russell tower schema while documenting the
precise extension still required before a first-class Tarski core may replace
it.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

namespace SchemaElaboration

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

/-! ## Reusable surface constructors -/

/-- A nondependent function type, represented by a dependent product whose
codomain is weakened across the fresh argument. -/
def arrow (domain codomain : Tower.Tm n) : Tower.Tm n :=
  .pi domain (Presentation.rename wk codomain)

/-- Renaming distributes through the derived nondependent arrow. -/
@[simp] theorem rename_arrow (renameMap : Ren n m)
    (domain codomain : Tower.Tm n) :
    Presentation.rename renameMap (arrow domain codomain) =
      arrow (Presentation.rename renameMap domain)
        (Presentation.rename renameMap codomain) := by
  simp [arrow, Presentation.rename, rename_comp]
  apply rename_ext
  intro i
  rfl

/-- Simultaneous substitution distributes through the derived arrow. -/
@[simp] theorem subst_arrow (sigma : Sub Tower.Head n m)
    (domain codomain : Tower.Tm n) :
    Presentation.subst sigma (arrow domain codomain) =
      arrow (Presentation.subst sigma domain)
        (Presentation.subst sigma codomain) := by
  simp [arrow, Presentation.subst, subst_liftSub_wk]

/-- Opening a nondependent arrow acts pointwise on its two endpoints. -/
@[simp] theorem inst0_arrow (argument : Tower.Tm n)
    (domain codomain : Tower.Tm (n + 1)) :
    Presentation.inst0 argument (arrow domain codomain) =
      arrow (Presentation.inst0 argument domain)
        (Presentation.inst0 argument codomain) := by
  exact subst_arrow (Presentation.subst0 argument) domain codomain

/-! ## The explicit polymorphic composition schema -/

def alpha : LevelExpr := .param 0
def beta : LevelExpr := .param 1
def gamma : LevelExpr := .param 2

/-- Context after the explicit binder `A : U alpha`. -/
def composeCtxA : Tower.Ctx 1 :=
  .snoc .nil (sortTm alpha)

/-- Context after `A : U alpha` and `B : U beta`. -/
def composeCtxAB : Tower.Ctx 2 :=
  .snoc composeCtxA (sortTm beta)

/-- Context after all three type binders.  In de Bruijn order, `C`, `B`, and
`A` have indices zero, one, and two. -/
def composeCtxABC : Tower.Ctx 3 :=
  .snoc composeCtxAB (sortTm gamma)

/-- The monomorphic body of functional composition in the three-type context:
`(A -> B) -> (B -> C) -> A -> C`. -/
def composeBodyType : Tower.Tm 3 :=
  .pi
    (arrow (.var 2) (.var 1))
    (.pi
      (arrow (.var 2) (.var 1))
      (.pi (.var 4) (.var 3)))

/-- Functional composition in the same context: `fun f g x => g (f x)`. -/
def composeBodyTerm : Tower.Tm 3 :=
  .lam (.lam (.lam (.app (.var 1) (.app (.var 2) (.var 0)))))

/-- Contexts introduced by the three term binders of composition. -/
def composeCtxABCF : Tower.Ctx 4 :=
  .snoc composeCtxABC (arrow (.var 2) (.var 1))

def composeCtxABCFG : Tower.Ctx 5 :=
  .snoc composeCtxABCF (arrow (.var 2) (.var 1))

def composeCtxABCFGX : Tower.Ctx 6 :=
  .snoc composeCtxABCFG (.var 4)

@[simp] theorem composeCtxABCFGX_lookup_x :
    Ctx.lookup composeCtxABCFGX 0 = (.var 5 : Tower.Tm 6) := by
  decide

@[simp] theorem composeCtxABCFGX_lookup_g :
    Ctx.lookup composeCtxABCFGX 1 = arrow (.var 4) (.var 3) := by
  decide

@[simp] theorem composeCtxABCFGX_lookup_f :
    Ctx.lookup composeCtxABCFGX 2 = arrow (.var 5) (.var 4) := by
  decide

/-- The level of the monomorphic composition body type. -/
def composeBodyLevel : LevelExpr :=
  .max (.max alpha beta)
    (.max (.max beta gamma) (.max alpha gamma))

/-- The closed schema type at three supplied levels.  Its first three products
are the lexical type binders `A : U levelA`, `B : U levelB`, and
`C : U levelC`. -/
def composeSchemaTypeAt (levelA levelB levelC : LevelExpr) : Tower.Tm 0 :=
  .pi (sortTm levelA)
    (.pi (sortTm levelB)
      (.pi (sortTm levelC) composeBodyType))

/-- The generic schema uses the first three admitted level parameters. -/
def composeSchemaType : Tower.Tm 0 :=
  composeSchemaTypeAt alpha beta gamma

/-- The closed schema implementation binds types as well as functions and the
argument. -/
def composeSchemaTerm : Tower.Tm 0 :=
  .lam (.lam (.lam composeBodyTerm))

/-- The universe level containing the closed composition schema type. -/
def composeSchemaLevel : LevelExpr :=
  .max (.succ alpha)
    (.max (.succ beta) (.max (.succ gamma) composeBodyLevel))

/-- Instantiating the schema's level parameters is literal level substitution
through the explicit target type. -/
@[simp] theorem composeSchemaType_substLevels (theta : Nat → LevelExpr) :
    RussellTarski.substLevelsTm theta composeSchemaType =
      composeSchemaTypeAt (theta 0) (theta 1) (theta 2) := by
  rfl

/-! ## Formation and inhabitation -/

/-- `A -> B` is a type in the three-type context. -/
theorem composeAB_hasType :
    Tower.HasType composeCtxABC (arrow (.var 2) (.var 1))
      (sortTm (.max alpha beta)) := by
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 2
  · exact .sort alpha
  · exact Presentation.HasType.var 2
  · exact .sort beta
  · exact .sorts alpha beta

/-- `B -> C` remains well formed after the function `f : A -> B` is bound. -/
theorem composeBC_afterF_hasType :
    Tower.HasType
      (.snoc composeCtxABC (arrow (.var 2) (.var 1)))
      (arrow (.var 2) (.var 1))
      (sortTm (.max beta gamma)) := by
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 2
  · exact .sort beta
  · exact Presentation.HasType.var 2
  · exact .sort gamma
  · exact .sorts beta gamma

/-- `A -> C` remains well formed after `f` and `g` are bound. -/
theorem composeAC_afterFG_hasType :
    Tower.HasType
      (.snoc
        (.snoc composeCtxABC (arrow (.var 2) (.var 1)))
        (arrow (.var 2) (.var 1)))
      (arrow (.var 4) (.var 2))
      (sortTm (.max alpha gamma)) := by
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 4
  · exact .sort alpha
  · exact Presentation.HasType.var 3
  · exact .sort gamma
  · exact .sorts alpha gamma

/-- The monomorphic composition signature is independently well formed. -/
theorem composeBodyType_hasType :
    Tower.HasType composeCtxABC composeBodyType (sortTm composeBodyLevel) := by
  unfold composeBodyType composeBodyLevel
  apply Presentation.HasType.piForm composeAB_hasType (.sort _)
  · apply Presentation.HasType.piForm composeBC_afterF_hasType (.sort _)
    · apply Presentation.HasType.piForm
      · exact Presentation.HasType.var 4
      · exact .sort alpha
      · exact Presentation.HasType.var 3
      · exact .sort gamma
      · exact .sorts alpha gamma
    · exact .sort (.max alpha gamma)
    · exact .sorts (.max beta gamma) (.max alpha gamma)
  · exact .sort (.max (.max beta gamma) (.max alpha gamma))
  · exact .sorts (.max alpha beta)
      (.max (.max beta gamma) (.max alpha gamma))

/-- The executable composition term inhabits its monomorphic signature. -/
theorem composeBodyTerm_hasType :
    Tower.HasType composeCtxABC composeBodyTerm composeBodyType := by
  unfold composeBodyTerm composeBodyType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  change Tower.HasType composeCtxABCFGX
    (.app (.var 1) (.app (.var 2) (.var 0))) (.var 3)
  have functionTyping : Tower.HasType composeCtxABCFGX (.var 2)
      (arrow (.var 5) (.var 4)) := by
    simpa only [composeCtxABCFGX_lookup_f] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := composeCtxABCFGX) 2)
  have argumentTyping : Tower.HasType composeCtxABCFGX (.var 0) (.var 5) := by
    simpa only [composeCtxABCFGX_lookup_x] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := composeCtxABCFGX) 0)
  have firstApplication : Tower.HasType composeCtxABCFGX
      (.app (.var 2) (.var 0)) (.var 4) := by
    simpa only [arrow, inst0_rename_wk] using
      (Presentation.HasType.appElim functionTyping argumentTyping)
  have continuationTyping : Tower.HasType composeCtxABCFGX (.var 1)
      (arrow (.var 4) (.var 3)) := by
    simpa only [composeCtxABCFGX_lookup_g] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := composeCtxABCFGX) 1)
  simpa only [arrow, inst0_rename_wk] using
    (Presentation.HasType.appElim continuationTyping firstApplication)

/-- The entire closed schema type is well formed at the stated universe. -/
theorem composeSchemaType_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) composeSchemaType
      (sortTm composeSchemaLevel) := by
  unfold composeSchemaType composeSchemaLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort alpha)
  · exact .sort (.succ alpha)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort beta)
    · exact .sort (.succ beta)
    · apply Presentation.HasType.piForm
      · exact .headType (.sort gamma)
      · exact .sort (.succ gamma)
      · exact composeBodyType_hasType
      · exact .sort composeBodyLevel
      · exact .sorts (.succ gamma) composeBodyLevel
    · exact .sort (.max (.succ gamma) composeBodyLevel)
    · exact .sorts (.succ beta) (.max (.succ gamma) composeBodyLevel)
  · exact .sort
      (.max (.succ beta) (.max (.succ gamma) composeBodyLevel))
  · exact .sorts (.succ alpha)
      (.max (.succ beta) (.max (.succ gamma) composeBodyLevel))

/-- The explicit six-binder composition program inhabits its closed type. -/
theorem composeSchemaTerm_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) composeSchemaTerm composeSchemaType := by
  unfold composeSchemaTerm composeSchemaType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  exact composeBodyTerm_hasType

/-- The present generated-code fragment deliberately refuses this schema:
its body contains neutral type variables.  A first-class Tarski core must add
typed neutral codes before it can claim the composition presentation theorem. -/
theorem composeSchema_outside_generated_code_image :
    RussellTarski.reify composeSchemaType = none := by
  decide

/-! ## Negative lexical-boundary witnesses -/

/-- The first type binder carries its declared universe; silently replacing
`A : U alpha` by a second `B : U beta` changes the schema. -/
theorem compose_type_binder_not_reclassifiable :
    composeSchemaType ≠
      (.pi (sortTm beta)
        (.pi (sortTm beta) (.pi (sortTm gamma) composeBodyType)) : Tower.Tm 0) := by
  decide

/-- A matcher-style free constant is not silently licensed as a type binder:
the generic tower has no rule assigning arbitrary constants a universe. -/
theorem typed_term_ne_const {Gamma : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Tower.HasType Gamma term type) (name : DeclName) :
    term ≠ .const name := by
  induction typing <;> simp_all [Tower.rules]

theorem matcher_constant_has_no_tower_type (name : DeclName) (level : LevelExpr) :
    ¬ Tower.HasType (.nil : Tower.Ctx 0) (.const name) (sortTm level) := by
  intro typing
  exact typed_term_ne_const typing name rfl

/-! ## A nondegenerate higher-order map: Church lists -/

/-- Result-universe parameter for the Church-list example. -/
def foldLevel : LevelExpr := .param 2

/-- The body obtained by instantiating a Church list at a result type:
`R -> (A -> R -> R) -> R`. -/
def churchFoldType (element result : Tower.Tm n) : Tower.Tm n :=
  arrow result (arrow (arrow element (arrow result result)) result)

/-- The portion of a Church-list code below its result-type binder. -/
def churchListBody (element : Tower.Tm n) : Tower.Tm (n + 1) :=
  .pi (.var 0)
    (.pi
      (arrow
        (Presentation.rename wk (Presentation.rename wk element))
        (arrow (.var 1) (.var 1)))
      (.var 2))

/-- Predicative Church lists.  The explicit result universe keeps this a
genuine higher-order encoding rather than a primitive or identity-container
masquerade:
`Pi (R : U resultLevel), R -> (A -> R -> R) -> R`. -/
def churchList (element : Tower.Tm n) (resultLevel : LevelExpr) : Tower.Tm n :=
  .pi (sortTm resultLevel) (churchListBody element)

/-- Opening the result-type binder computes the advertised fold signature. -/
@[simp] theorem churchList_instantiates (element result : Tower.Tm n) :
    inst0 result (churchListBody element) =
      churchFoldType element result := by
  have elementLifted :
      Presentation.subst (liftSub (subst0 result))
          (Presentation.rename wk (Presentation.rename wk element)) =
        Presentation.rename wk element := by
    rw [subst_liftSub_wk]
    congr 1
    exact inst0_rename_wk result element
  have resultLiftedOnce :
      liftSub (subst0 result) (1 : Fin (n + 2)) =
        Presentation.rename wk result := by
    rfl
  have resultLiftedTwice :
      liftSub (liftSub (subst0 result)) (2 : Fin (n + 3)) =
        Presentation.rename wk (Presentation.rename wk result) := by
    rfl
  simp only [churchListBody, inst0, Presentation.subst]
  rw [subst0_zero, subst_arrow, elementLifted, subst_arrow, subst_var,
    resultLiftedOnce, resultLiftedTwice]
  unfold churchFoldType
  apply congrArg (Tm.pi result)
  simp only [rename_arrow]
  rfl

/-- The higher-order map signature after its lexical type binders:
`(A -> B) -> ChurchList A -> ChurchList B`. -/
def churchMapBodyType : Tower.Tm 2 :=
  arrow (arrow (.var 1) (.var 0))
    (arrow (churchList (.var 1) foldLevel) (churchList (.var 0) foldLevel))

/-- Church map is implemented by changing the fold step:
`fun f xs R z c => xs R z (fun a r => c (f a) r)`. -/
def churchMapBodyTerm : Tower.Tm 2 :=
  .lam (.lam (.lam (.lam (.lam
    (.app
      (.app (.app (.var 3) (.var 2)) (.var 1))
      (.lam (.lam
        (.app (.app (.var 2) (.app (.var 6) (.var 1))) (.var 0)))))))))

/-- Closed schema type with explicit `A : U alpha` and `B : U beta`
binders. -/
def churchMapSchemaType : Tower.Tm 0 :=
  .pi (sortTm alpha) (.pi (sortTm beta) churchMapBodyType)

def churchMapSchemaTerm : Tower.Tm 0 :=
  .lam (.lam churchMapBodyTerm)

/-! ### Contexts and independently checked lookup facts -/

def churchMapCtxABF : Tower.Ctx 3 :=
  .snoc composeCtxAB (arrow (.var 1) (.var 0))

def churchMapCtxABFXs : Tower.Ctx 4 :=
  .snoc churchMapCtxABF
    (Presentation.rename wk (churchList (.var 1) foldLevel))

def churchMapCtxABFXsR : Tower.Ctx 5 :=
  .snoc churchMapCtxABFXs (sortTm foldLevel)

def churchMapCtxABFXsRZ : Tower.Ctx 6 :=
  .snoc churchMapCtxABFXsR (.var 0)

def churchMapCtxABFXsRZC : Tower.Ctx 7 :=
  .snoc churchMapCtxABFXsRZ
    (arrow (.var 4) (arrow (.var 1) (.var 1)))

@[simp] theorem churchMap_lookup_xs :
    Ctx.lookup churchMapCtxABFXsRZC 3 = churchList (.var 6) foldLevel := by
  decide

@[simp] theorem churchMap_lookup_resultType :
    Ctx.lookup churchMapCtxABFXsRZC 2 = sortTm foldLevel := by
  decide

@[simp] theorem churchMap_lookup_seed :
    Ctx.lookup churchMapCtxABFXsRZC 1 = (.var 2 : Tower.Tm 7) := by
  decide

@[simp] theorem churchMap_lookup_step :
    Ctx.lookup churchMapCtxABFXsRZC 0 =
      arrow (.var 5) (arrow (.var 2) (.var 2)) := by
  decide

@[simp] theorem churchMap_lookup_function :
    Ctx.lookup churchMapCtxABFXsRZC 4 = arrow (.var 6) (.var 5) := by
  decide

/-! ### Independent formation of the Church-list types -/

def churchStepLevel (elementLevel resultLevel : LevelExpr) : LevelExpr :=
  .max elementLevel (.max resultLevel resultLevel)

def churchBodyLevel (elementLevel resultLevel : LevelExpr) : LevelExpr :=
  .max resultLevel (.max (churchStepLevel elementLevel resultLevel) resultLevel)

def churchListLevel (elementLevel resultLevel : LevelExpr) : LevelExpr :=
  .max (.succ resultLevel) (churchBodyLevel elementLevel resultLevel)

/-- Generic formation for a Church list whose element type is a lexical
context variable.  This is the reusable schema case needed after additional
function and list binders have shifted the original type parameter. -/
theorem churchList_var_hasType {Gamma : Tower.Ctx n} (i : Fin n)
    (elementLevel : LevelExpr)
    (lookupElement : Ctx.lookup Gamma i = sortTm elementLevel) :
    Tower.HasType Gamma (churchList (.var i) foldLevel)
      (sortTm (churchListLevel elementLevel foldLevel)) := by
  unfold churchList churchListBody churchListLevel churchBodyLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort foldLevel)
  · exact .sort (.succ foldLevel)
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 0
    · exact .sort foldLevel
    · apply Presentation.HasType.piForm
      · change Tower.HasType
          (.snoc (.snoc Gamma (sortTm foldLevel)) (.var 0))
          (arrow (.var i.succ.succ) (arrow (.var 1) (.var 1)))
          (sortTm (churchStepLevel elementLevel foldLevel))
        unfold churchStepLevel
        apply Presentation.HasType.piForm
        · simpa [Ctx.lookup, lookupElement, sortTm,
            Presentation.rename] using
            (Presentation.HasType.var (R := Tower.rules)
              (Γ := .snoc (.snoc Gamma (sortTm foldLevel)) (.var 0)) i.succ.succ)
        · exact .sort elementLevel
        · change Tower.HasType
            (.snoc
              (.snoc (.snoc Gamma (sortTm foldLevel)) (.var 0))
              (.var i.succ.succ))
            (arrow (.var 2) (.var 2)) (sortTm (.max foldLevel foldLevel))
          apply Presentation.HasType.piForm
          · exact Presentation.HasType.var 2
          · exact .sort foldLevel
          · exact Presentation.HasType.var 3
          · exact .sort foldLevel
          · exact .sorts foldLevel foldLevel
        · exact .sort (.max foldLevel foldLevel)
        · exact .sorts elementLevel (.max foldLevel foldLevel)
      · exact .sort (churchStepLevel elementLevel foldLevel)
      · exact Presentation.HasType.var 2
      · exact .sort foldLevel
      · exact .sorts (churchStepLevel elementLevel foldLevel) foldLevel
    · exact .sort (.max (churchStepLevel elementLevel foldLevel) foldLevel)
    · exact .sorts foldLevel (.max (churchStepLevel elementLevel foldLevel) foldLevel)
  · exact .sort (churchBodyLevel elementLevel foldLevel)
  · exact .sorts (.succ foldLevel) (churchBodyLevel elementLevel foldLevel)

theorem composeCtxAB_lookup_A : Ctx.lookup composeCtxAB 1 = sortTm alpha := by
  decide

theorem composeCtxAB_lookup_B : Ctx.lookup composeCtxAB 0 = sortTm beta := by
  decide

/-- Both input and output Church-list constructors are genuine formed types,
as instances of the generic lexical-variable theorem. -/
theorem churchListA_hasType :
    Tower.HasType composeCtxAB (churchList (.var 1) foldLevel)
      (sortTm (churchListLevel alpha foldLevel)) :=
  churchList_var_hasType 1 alpha composeCtxAB_lookup_A

theorem churchListB_hasType :
    Tower.HasType composeCtxAB (churchList (.var 0) foldLevel)
      (sortTm (churchListLevel beta foldLevel)) :=
  churchList_var_hasType 0 beta composeCtxAB_lookup_B

/-! ### Independent formation of the map signature -/

def churchMapFunctionLevel : LevelExpr := .max alpha beta

def churchMapInnerLevel : LevelExpr :=
  .max (churchListLevel alpha foldLevel) (churchListLevel beta foldLevel)

def churchMapBodyLevel : LevelExpr :=
  .max churchMapFunctionLevel churchMapInnerLevel

def churchMapSchemaLevel : LevelExpr :=
  .max (.succ alpha) (.max (.succ beta) churchMapBodyLevel)

theorem churchMapFunction_hasType :
    Tower.HasType composeCtxAB (arrow (.var 1) (.var 0))
      (sortTm churchMapFunctionLevel) := by
  unfold churchMapFunctionLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 1
  · exact .sort alpha
  · exact Presentation.HasType.var 1
  · exact .sort beta
  · exact .sorts alpha beta

theorem churchMapCtxABF_lookup_A :
    Ctx.lookup churchMapCtxABF 2 = sortTm alpha := by
  decide

theorem churchMapCtxABF_lookup_B :
    Ctx.lookup churchMapCtxABF 1 = sortTm beta := by
  decide

theorem churchMapCtxABFXs_lookup_B :
    Ctx.lookup churchMapCtxABFXs 2 = sortTm beta := by
  decide

theorem churchListA_afterF_hasType :
    Tower.HasType churchMapCtxABF (churchList (.var 2) foldLevel)
      (sortTm (churchListLevel alpha foldLevel)) :=
  churchList_var_hasType 2 alpha churchMapCtxABF_lookup_A

theorem churchListB_afterF_hasType :
    Tower.HasType churchMapCtxABF (churchList (.var 1) foldLevel)
      (sortTm (churchListLevel beta foldLevel)) :=
  churchList_var_hasType 1 beta churchMapCtxABF_lookup_B

theorem churchListB_afterFXs_hasType :
    Tower.HasType churchMapCtxABFXs (churchList (.var 2) foldLevel)
      (sortTm (churchListLevel beta foldLevel)) :=
  churchList_var_hasType 2 beta churchMapCtxABFXs_lookup_B

/-- Weakening the inner map arrow across `f` produces exactly the two shifted
Church-list parameters. -/
theorem churchMapInner_rename :
    Presentation.rename (wk : Ren 2 3)
      (arrow (churchList (.var 1) foldLevel) (churchList (.var 0) foldLevel) :
        Tower.Tm 2) =
    (arrow (churchList (.var 2) foldLevel) (churchList (.var 1) foldLevel) :
      Tower.Tm 3) := by
  decide

theorem churchMapInner_afterF_hasType :
    Tower.HasType churchMapCtxABF
      (arrow (churchList (.var 2) foldLevel) (churchList (.var 1) foldLevel))
      (sortTm churchMapInnerLevel) := by
  unfold churchMapInnerLevel
  apply Presentation.HasType.piForm
  · exact churchListA_afterF_hasType
  · exact .sort (churchListLevel alpha foldLevel)
  · exact churchListB_afterFXs_hasType
  · exact .sort (churchListLevel beta foldLevel)
  · exact .sorts (churchListLevel alpha foldLevel) (churchListLevel beta foldLevel)

/-- The full higher-order map body signature is a formed tower type. -/
theorem churchMapBodyType_hasType :
    Tower.HasType composeCtxAB churchMapBodyType
      (sortTm churchMapBodyLevel) := by
  unfold churchMapBodyType churchMapBodyLevel
  apply Presentation.HasType.piForm
  · exact churchMapFunction_hasType
  · exact .sort churchMapFunctionLevel
  · rw [churchMapInner_rename]
    exact churchMapInner_afterF_hasType
  · exact .sort churchMapInnerLevel
  · exact .sorts churchMapFunctionLevel churchMapInnerLevel

/-- The two type binders and the map body together form a closed schema type. -/
theorem churchMapSchemaType_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) churchMapSchemaType
      (sortTm churchMapSchemaLevel) := by
  unfold churchMapSchemaType churchMapSchemaLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort alpha)
  · exact .sort (.succ alpha)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort beta)
    · exact .sort (.succ beta)
    · exact churchMapBodyType_hasType
    · exact .sort churchMapBodyLevel
    · exact .sorts (.succ beta) churchMapBodyLevel
  · exact .sort (.max (.succ beta) churchMapBodyLevel)
  · exact .sorts (.succ alpha) (.max (.succ beta) churchMapBodyLevel)

/-! ### The map derivation -/

/-- The fold step synthesized by map in the final five-binder context. -/
def churchMapStepTerm : Tower.Tm 7 :=
  .lam (.lam
    (.app (.app (.var 2) (.app (.var 6) (.var 1))) (.var 0)))

def churchMapStepCtxA : Tower.Ctx 8 :=
  .snoc churchMapCtxABFXsRZC (.var 6)

def churchMapStepCtxAR : Tower.Ctx 9 :=
  .snoc churchMapStepCtxA (.var 3)

@[simp] theorem churchMapStep_lookup_r :
    Ctx.lookup churchMapStepCtxAR 0 = (.var 4 : Tower.Tm 9) := by
  decide

@[simp] theorem churchMapStep_lookup_a :
    Ctx.lookup churchMapStepCtxAR 1 = (.var 8 : Tower.Tm 9) := by
  decide

@[simp] theorem churchMapStep_lookup_c :
    Ctx.lookup churchMapStepCtxAR 2 =
      arrow (.var 7) (arrow (.var 4) (.var 4)) := by
  decide

@[simp] theorem churchMapStep_lookup_f :
    Ctx.lookup churchMapStepCtxAR 6 = arrow (.var 8) (.var 7) := by
  decide

/-- The synthesized fold step maps each `A` through `f` before passing it to
the output algebra. -/
theorem churchMapStep_hasType :
    Tower.HasType churchMapCtxABFXsRZC churchMapStepTerm
      (arrow (.var 6) (arrow (.var 2) (.var 2))) := by
  unfold churchMapStepTerm
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  change Tower.HasType churchMapStepCtxAR
    (.app (.app (.var 2) (.app (.var 6) (.var 1))) (.var 0)) (.var 4)
  have functionTyping : Tower.HasType churchMapStepCtxAR (.var 6)
      (arrow (.var 8) (.var 7)) := by
    simpa only [churchMapStep_lookup_f] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapStepCtxAR) 6)
  have elementTyping : Tower.HasType churchMapStepCtxAR (.var 1) (.var 8) := by
    simpa only [churchMapStep_lookup_a] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapStepCtxAR) 1)
  have mappedTyping : Tower.HasType churchMapStepCtxAR
      (.app (.var 6) (.var 1)) (.var 7) := by
    simpa only [arrow, inst0_rename_wk] using
      (Presentation.HasType.appElim functionTyping elementTyping)
  have stepTyping : Tower.HasType churchMapStepCtxAR (.var 2)
      (arrow (.var 7) (arrow (.var 4) (.var 4))) := by
    simpa only [churchMapStep_lookup_c] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapStepCtxAR) 2)
  have steppedTyping : Tower.HasType churchMapStepCtxAR
      (.app (.var 2) (.app (.var 6) (.var 1)))
      (arrow (.var 4) (.var 4)) := by
    simpa only [arrow, inst0_rename_wk] using
      (Presentation.HasType.appElim stepTyping mappedTyping)
  have resultTyping : Tower.HasType churchMapStepCtxAR (.var 0) (.var 4) := by
    simpa only [churchMapStep_lookup_r] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapStepCtxAR) 0)
  simpa only [arrow, inst0_rename_wk] using
    (Presentation.HasType.appElim steppedTyping resultTyping)

/-- Folding the input Church list with the synthesized step produces the
requested result carrier. -/
theorem churchMapFold_hasType :
    Tower.HasType churchMapCtxABFXsRZC
      (.app
        (.app (.app (.var 3) (.var 2)) (.var 1))
        churchMapStepTerm)
      (.var 2) := by
  have listTyping : Tower.HasType churchMapCtxABFXsRZC (.var 3)
      (churchList (.var 6) foldLevel) := by
    simpa only [churchMap_lookup_xs] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapCtxABFXsRZC) 3)
  have resultTypeTyping : Tower.HasType churchMapCtxABFXsRZC (.var 2)
      (sortTm foldLevel) := by
    simpa only [churchMap_lookup_resultType] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapCtxABFXsRZC) 2)
  have instantiated : Tower.HasType churchMapCtxABFXsRZC
      (.app (.var 3) (.var 2))
      (churchFoldType (.var 6) (.var 2)) := by
    simpa only [churchList, churchList_instantiates] using
      (Presentation.HasType.appElim listTyping resultTypeTyping)
  have seedTyping : Tower.HasType churchMapCtxABFXsRZC (.var 1) (.var 2) := by
    simpa only [churchMap_lookup_seed] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := churchMapCtxABFXsRZC) 1)
  have seeded : Tower.HasType churchMapCtxABFXsRZC
      (.app (.app (.var 3) (.var 2)) (.var 1))
      (arrow (arrow (.var 6) (arrow (.var 2) (.var 2))) (.var 2)) := by
    simpa only [churchFoldType, arrow, inst0_rename_wk] using
      (Presentation.HasType.appElim instantiated seedTyping)
  simpa only [arrow, inst0_rename_wk] using
    (Presentation.HasType.appElim seeded churchMapStep_hasType)

/-- The higher-order Church map implementation inhabits its explicit
two-type schema body. -/
theorem churchMapBodyTerm_hasType :
    Tower.HasType composeCtxAB churchMapBodyTerm churchMapBodyType := by
  unfold churchMapBodyTerm churchMapBodyType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  change Tower.HasType churchMapCtxABFXsRZC
    (.app
      (.app (.app (.var 3) (.var 2)) (.var 1))
      churchMapStepTerm)
    (.var 2)
  exact churchMapFold_hasType

/-- The closed Church-map schema is inhabited after its type binders become
lexical products. -/
theorem churchMapSchemaTerm_hasType :
    Tower.HasType (.nil : Tower.Ctx 0)
      churchMapSchemaTerm churchMapSchemaType := by
  unfold churchMapSchemaTerm churchMapSchemaType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  exact churchMapBodyTerm_hasType

/-- Negative witness: Church map is not the two-argument projection that
would ignore both the algebra and every list element. -/
theorem churchMap_is_not_second_projection :
    churchMapBodyTerm ≠ (.lam (.lam (.var 0)) : Tower.Tm 2) := by
  decide

end SchemaElaboration

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
