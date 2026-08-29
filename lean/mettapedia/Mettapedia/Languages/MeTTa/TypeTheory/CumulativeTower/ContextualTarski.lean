import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RussellTarskiBoundary
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature

/-!
# Contextual Tarski codes with typed template instantiation

The generated code fragment is closed under binders but has no neutral code
hypotheses.  Adding an unrestricted constructor containing an arbitrary tower
term would make reification vacuous.  Instead, a neutral code occurrence names
a contextual template and carries an explicit substitution from that
template's declaration telescope into the current telescope.

Formation checks that substitution.  Consequently a template may represent
an open type family such as `B x`, term substitution is total and coherent,
and arbitrary raw terms do not silently acquire code authority.  The former
generated code grammar is recovered exactly as the zero-template fragment.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace RussellTarski
namespace Contextual

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

/-! ## Typed contextual templates -/

/-- A neutral code template is a type expression in a well-formed declaration
telescope.  Each occurrence must provide a typed substitution for this
telescope. -/
structure Template where
  arity : Nat
  context : Tower.Ctx arity
  contextWellFormed : Declaration.ContextWellFormed Tower.rules context
  body : Tower.Tm arity
  level : LevelExpr
  bodyTyping : Tower.HasType context body (sortTm level)

abbrev TemplateSignature (count : Nat) := Fin count → Template

/-! ## The free contextual extension of generated codes -/

/-- Generated Tarski constructors plus proof-relevant references to
contextual templates.  The substitution stored by `template` is raw syntax;
`HasCode` below is what licenses it. -/
inductive Code {count : Nat} (templates : TemplateSignature count) :
    Nat → Type where
  | template {n : Nat} (name : Fin count)
      (arguments : Sub Tower.Head (templates name).arity n) : Code templates n
  | ground {n : Nat} : Code templates n
  | univ {n : Nat} (level : LevelExpr) : Code templates n
  | pi {n : Nat} : Code templates n → Code templates (n + 1) → Code templates n
  | sigma {n : Nat} :
      Code templates n → Code templates (n + 1) → Code templates n
  | id {n : Nat} :
      Code templates n → Tower.Tm n → Tower.Tm n → Code templates n
  | lift {n : Nat} :
      LevelExpr → LevelExpr → Code templates n → Code templates n

/-- Decode a contextual template occurrence by applying its stored
substitution; all generated constructors remain structural. -/
def decode {templates : TemplateSignature count} :
    Code templates n → Tower.Tm n
  | .template name arguments =>
      Presentation.subst arguments (templates name).body
  | .ground => .head .legacyGround
  | .univ level => .head (.sort level)
  | .pi domain codomain => .pi (decode domain) (decode codomain)
  | .sigma domain codomain => .sigma (decode domain) (decode codomain)
  | .id type left right => .id (decode type) left right
  | .lift _ _ code => decode code

/-! ## Term substitution and its laws -/

/-- Substitute ordinary tower terms through a contextual code.  At a
template occurrence this composes the occurrence's contextual arguments. -/
def Code.subst {templates : TemplateSignature count}
    (substitution : Sub Tower.Head n m) :
    Code templates n → Code templates m
  | .template name arguments =>
      .template name (subComp substitution arguments)
  | .ground => .ground
  | .univ level => .univ level
  | .pi domain codomain =>
      .pi (domain.subst substitution) (codomain.subst (liftSub substitution))
  | .sigma domain codomain =>
      .sigma (domain.subst substitution)
        (codomain.subst (liftSub substitution))
  | .id type left right =>
      .id (type.subst substitution)
        (Presentation.subst substitution left)
        (Presentation.subst substitution right)
  | .lift source target code => .lift source target (code.subst substitution)

/-- Renaming is the variable-only case of contextual substitution. -/
def Code.rename {templates : TemplateSignature count} (rho : Ren n m)
    (code : Code templates n) : Code templates m :=
  code.subst (renSub rho)

/-- Decoding commutes with arbitrary term substitution, including template
instantiation beneath dependent binders. -/
@[simp] theorem decode_subst {templates : TemplateSignature count}
    (substitution : Sub Tower.Head n m) (code : Code templates n) :
    decode (code.subst substitution) =
      Presentation.subst substitution (decode code) := by
  induction code generalizing m with
  | template name arguments =>
      exact (subst_subComp substitution arguments (templates name).body).symm
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp only [Code.subst, decode, Presentation.subst, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [Code.subst, decode, Presentation.subst, ihDomain, ihCodomain]
  | id type left right ihType =>
      simp only [Code.subst, decode, Presentation.subst, ihType]
  | lift source target code ih => simp only [Code.subst, decode, ih]

/-- Decoding commutes with term-variable renaming. -/
@[simp] theorem decode_rename {templates : TemplateSignature count}
    (rho : Ren n m) (code : Code templates n) :
    decode (code.rename rho) = Presentation.rename rho (decode code) := by
  rw [Code.rename, decode_subst, subst_renSub]

@[simp] theorem Code.subst_ids {templates : TemplateSignature count}
    (code : Code templates n) :
    code.subst (ids (Head := Tower.Head)) = code := by
  induction code with
  | template name arguments =>
      simp [Code.subst, subComp_ids_left]
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [Code.subst, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [Code.subst, ihDomain, ihCodomain]
  | id type left right ihType => simp [Code.subst, ihType]
  | lift source target code ih => simp [Code.subst, ih]

@[simp] theorem Code.subst_comp {templates : TemplateSignature count}
    (later : Sub Tower.Head m k) (earlier : Sub Tower.Head n m)
    (code : Code templates n) :
    (code.subst earlier).subst later =
      code.subst (subComp later earlier) := by
  induction code generalizing m k with
  | template name arguments =>
      simp only [Code.subst]
      congr 1
      exact subComp_assoc later earlier arguments
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp only [Code.subst]
      congr 1
      · exact ihDomain later earlier
      · rw [ihCodomain]
        apply congrArg (fun substitution => codomain.subst substitution)
        funext index
        exact liftSub_comp_apply later earlier index
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [Code.subst]
      congr 1
      · exact ihDomain later earlier
      · rw [ihCodomain]
        apply congrArg (fun substitution => codomain.subst substitution)
        funext index
        exact liftSub_comp_apply later earlier index
  | id type left right ihType =>
      simp only [Code.subst]
      congr 1
      · exact ihType later earlier
      · change Presentation.subst later (Presentation.subst earlier left) =
          Presentation.subst (fun i => Presentation.subst later (earlier i)) left
        exact Presentation.subst_comp later earlier left
      · change Presentation.subst later (Presentation.subst earlier right) =
          Presentation.subst (fun i => Presentation.subst later (earlier i)) right
        exact Presentation.subst_comp later earlier right
  | lift source target code ih => simp [Code.subst, ih]

/-! ## Formation -/

/-- Formation of contextual codes.  A template is admitted only through a
typed substitution from its declaration telescope. -/
inductive HasCode {templates : TemplateSignature count} :
    Tower.Ctx n → Code templates n → LevelExpr → Prop where
  | template {Gamma : Tower.Ctx n} {name : Fin count}
      {arguments : Sub Tower.Head (templates name).arity n} :
      CtxMor Tower.rules (templates name).context Gamma arguments →
      HasCode Gamma (.template name arguments) (templates name).level
  | ground {Gamma : Tower.Ctx n} : HasCode Gamma .ground Tower.zero
  | univ {Gamma : Tower.Ctx n} (level : LevelExpr) :
      HasCode Gamma (.univ level) (.succ level)
  | pi {Gamma : Tower.Ctx n} {domain : Code templates n}
      {codomain : Code templates (n + 1)}
      {domainLevel codomainLevel : LevelExpr} :
      HasCode Gamma domain domainLevel →
      HasCode (.snoc Gamma (decode domain)) codomain codomainLevel →
      HasCode Gamma (.pi domain codomain) (.max domainLevel codomainLevel)
  | sigma {Gamma : Tower.Ctx n} {domain : Code templates n}
      {codomain : Code templates (n + 1)}
      {domainLevel codomainLevel : LevelExpr} :
      HasCode Gamma domain domainLevel →
      HasCode (.snoc Gamma (decode domain)) codomain codomainLevel →
      HasCode Gamma (.sigma domain codomain) (.max domainLevel codomainLevel)
  | id {Gamma : Tower.Ctx n} {type : Code templates n}
      {left right : Tower.Tm n} {level : LevelExpr} :
      HasCode Gamma type level →
      Tower.HasType Gamma left (decode type) →
      Tower.HasType Gamma right (decode type) →
      HasCode Gamma (.id type left right) level
  | lift {Gamma : Tower.Ctx n} {code : Code templates n}
      {source target : LevelExpr} :
      HasCode Gamma code source →
      Tower.Cumulative (.sort source) (.sort target) →
      HasCode Gamma (.lift source target code) target

/-- Contextual code formation is stable under every typed term
substitution. -/
theorem HasCode.substitute {templates : TemplateSignature count}
    {Gamma : Tower.Ctx n} {code : Code templates n} {level : LevelExpr}
    (formation : HasCode Gamma code level)
    {Delta : Tower.Ctx m} {substitution : Sub Tower.Head n m}
    (typed : CtxMor Tower.rules Gamma Delta substitution) :
    HasCode Delta (code.subst substitution) level := by
  induction formation generalizing m with
  | template templateArguments =>
      exact .template (CtxMor.comp templateArguments typed)
  | ground => exact .ground
  | univ level => exact .univ level
  | pi domainFormation codomainFormation ihDomain ihCodomain =>
      apply HasCode.pi (ihDomain typed)
      simpa only [Code.subst, decode_subst] using
        ihCodomain (CtxMor.lift typed (decode _))
  | sigma domainFormation codomainFormation ihDomain ihCodomain =>
      apply HasCode.sigma (ihDomain typed)
      simpa only [Code.subst, decode_subst] using
        ihCodomain (CtxMor.lift typed (decode _))
  | id typeFormation leftTyping rightTyping ihType =>
      exact HasCode.id (ihType typed)
        (by simpa only [decode_subst] using leftTyping.substitute typed)
        (by simpa only [decode_subst] using rightTyping.substitute typed)
  | lift codeFormation order ihCode => exact .lift (ihCode typed) order

/-- Every formed contextual code decodes to an independently well-typed
Russell type. -/
theorem HasCode.decode_hasType {templates : TemplateSignature count}
    {Gamma : Tower.Ctx n} {code : Code templates n} {level : LevelExpr}
    (formation : HasCode Gamma code level) :
    Tower.HasType Gamma (decode code) (sortTm level) := by
  induction formation with
  | @template n Gamma name arguments typed =>
      simpa [decode, sortTm, Presentation.subst] using
        (templates name).bodyTyping.substitute typed
  | ground => exact .headType .legacyGround
  | univ level => exact .headType (.sort level)
  | pi domainFormation codomainFormation ihDomain ihCodomain =>
      exact .piForm ihDomain (.sort _) ihCodomain (.sort _) (.sorts _ _)
  | sigma domainFormation codomainFormation ihDomain ihCodomain =>
      exact .sigmaForm ihDomain (.sort _) ihCodomain (.sort _) (.sorts _ _)
  | id typeFormation leftTyping rightTyping ihType =>
      exact .idForm ihType (.sort _) leftTyping rightTyping
  | lift codeFormation order ihCode => exact .cumul ihCode order

/-- The level of a template occurrence is fixed by its declaration. -/
theorem template_level_unique {templates : TemplateSignature count}
    {Gamma : Tower.Ctx n} {name : Fin count}
    {arguments : Sub Tower.Head (templates name).arity n}
    {level : LevelExpr}
    (formation : @HasCode count templates n Gamma
      (@Code.template count templates n name arguments) level) :
    level = (templates name).level := by
  cases formation
  rfl

/-! ## The old generated grammar is exactly the zero-template fragment -/

def noTemplates : TemplateSignature 0 := Fin.elim0

def ofGenerated : RussellTarski.Code n → Code noTemplates n
  | .ground => .ground
  | .univ level => .univ level
  | .pi domain codomain => .pi (ofGenerated domain) (ofGenerated codomain)
  | .sigma domain codomain =>
      .sigma (ofGenerated domain) (ofGenerated codomain)
  | .id type left right => .id (ofGenerated type) left right
  | .lift source target code => .lift source target (ofGenerated code)

def toGenerated : Code noTemplates n → RussellTarski.Code n
  | .template name _ => Fin.elim0 name
  | .ground => .ground
  | .univ level => .univ level
  | .pi domain codomain => .pi (toGenerated domain) (toGenerated codomain)
  | .sigma domain codomain =>
      .sigma (toGenerated domain) (toGenerated codomain)
  | .id type left right => .id (toGenerated type) left right
  | .lift source target code => .lift source target (toGenerated code)

@[simp] theorem toGenerated_ofGenerated (code : RussellTarski.Code n) :
    toGenerated (ofGenerated code) = code := by
  induction code with
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, toGenerated, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, toGenerated, ihDomain, ihCodomain]
  | id type left right ihType => simp [ofGenerated, toGenerated, ihType]
  | lift source target code ih => simp [ofGenerated, toGenerated, ih]

@[simp] theorem ofGenerated_toGenerated (code : Code noTemplates n) :
    ofGenerated (toGenerated code) = code := by
  induction code with
  | template name arguments => exact Fin.elim0 name
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, toGenerated, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, toGenerated, ihDomain, ihCodomain]
  | id type left right ihType => simp [ofGenerated, toGenerated, ihType]
  | lift source target code ih => simp [ofGenerated, toGenerated, ih]

/-- The generated grammar is recovered by equivalence, rather than retained
as a competing foundation. -/
def generatedEquiv (n : Nat) : Code noTemplates n ≃ RussellTarski.Code n where
  toFun := toGenerated
  invFun := ofGenerated
  left_inv := ofGenerated_toGenerated
  right_inv := toGenerated_ofGenerated

@[simp] theorem decode_ofGenerated (code : RussellTarski.Code n) :
    decode (ofGenerated code) = RussellTarski.decode code := by
  induction code with
  | ground => rfl
  | univ level => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, decode, RussellTarski.decode, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [ofGenerated, decode, RussellTarski.decode, ihDomain, ihCodomain]
  | id type left right ihType =>
      simp [ofGenerated, decode, RussellTarski.decode, ihType]
  | lift source target code ih =>
      simp [ofGenerated, decode, RussellTarski.decode, ih]

@[simp] theorem decode_eq_generated_decode (code : Code noTemplates n) :
    decode code = RussellTarski.decode (toGenerated code) := by
  calc
    decode code = decode (ofGenerated (toGenerated code)) := by
      rw [ofGenerated_toGenerated]
    _ = RussellTarski.decode (toGenerated code) := decode_ofGenerated _

def HasCode.ofGenerated {Gamma : Tower.Ctx n}
    {code : RussellTarski.Code n} {level : LevelExpr}
    (formation : RussellTarski.HasCode Gamma code level) :
    Contextual.HasCode Gamma (ofGenerated code) level := by
  induction formation with
  | ground => exact .ground
  | univ level => exact .univ level
  | pi domainFormation codomainFormation ihDomain ihCodomain =>
      exact .pi ihDomain (by simpa only [decode_ofGenerated] using ihCodomain)
  | sigma domainFormation codomainFormation ihDomain ihCodomain =>
      exact .sigma ihDomain
        (by simpa only [decode_ofGenerated] using ihCodomain)
  | id typeFormation leftTyping rightTyping ihType =>
      exact .id ihType
        (by simpa only [decode_ofGenerated] using leftTyping)
        (by simpa only [decode_ofGenerated] using rightTyping)
  | lift codeFormation order ihCode => exact .lift ihCode order

def HasCode.toGenerated {Gamma : Tower.Ctx n}
    {code : Code noTemplates n} {level : LevelExpr}
    (formation : Contextual.HasCode Gamma code level) :
    RussellTarski.HasCode Gamma (toGenerated code) level := by
  induction formation with
  | @template n Gamma name arguments templateArguments =>
      exact Fin.elim0 name
  | ground => exact .ground
  | univ level => exact .univ level
  | pi domainFormation codomainFormation ihDomain ihCodomain =>
      exact .pi ihDomain
        (by simpa only [decode_eq_generated_decode] using ihCodomain)
  | sigma domainFormation codomainFormation ihDomain ihCodomain =>
      exact .sigma ihDomain
        (by simpa only [decode_eq_generated_decode] using ihCodomain)
  | id typeFormation leftTyping rightTyping ihType =>
      exact .id ihType
        (by simpa only [decode_eq_generated_decode] using leftTyping)
        (by simpa only [decode_eq_generated_decode] using rightTyping)
  | lift codeFormation order ihCode => exact .lift ihCode order

theorem generated_hasCode_iff {Gamma : Tower.Ctx n}
    (code : RussellTarski.Code n) (level : LevelExpr) :
    Contextual.HasCode Gamma (ofGenerated code) level ↔
      RussellTarski.HasCode Gamma code level := by
  constructor
  · intro formation
    simpa using formation.toGenerated
  · exact HasCode.ofGenerated

/-! ## A genuine open type-family template -/

def familyDomainLevel : LevelExpr := .param 20
def familyCodomainLevel : LevelExpr := .param 21

def familyContextA : Tower.Ctx 1 :=
  .snoc .nil (sortTm familyDomainLevel)

def familyType : Tower.Tm 1 :=
  .pi (.var 0) (sortTm familyCodomainLevel)

def familyContextAB : Tower.Ctx 2 :=
  .snoc familyContextA familyType

def familyContextABX : Tower.Ctx 3 :=
  .snoc familyContextAB (.var 1)

def familyBody : Tower.Tm 3 := .app (.var 1) (.var 0)

theorem familyType_hasType :
    Tower.HasType familyContextA familyType
      (sortTm (.max familyDomainLevel (.succ familyCodomainLevel))) := by
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 0
  · exact .sort familyDomainLevel
  · exact .headType (.sort familyCodomainLevel)
  · exact .sort (.succ familyCodomainLevel)
  · exact .sorts familyDomainLevel (.succ familyCodomainLevel)

theorem familyBody_hasType :
    Tower.HasType familyContextABX familyBody
      (sortTm familyCodomainLevel) := by
  have familyTyping : Tower.HasType familyContextABX (.var 1)
      (.pi (.var 2) (sortTm familyCodomainLevel)) := by
    exact Presentation.HasType.var 1
  have argumentTyping : Tower.HasType familyContextABX (.var 0) (.var 2) := by
    exact Presentation.HasType.var 0
  have application := Presentation.HasType.appElim familyTyping argumentTyping
  simpa [familyBody, sortTm, Presentation.inst0, Presentation.subst] using
    application

def familyTemplate : Template where
  arity := 3
  context := familyContextABX
  contextWellFormed := by
    apply Declaration.ContextWellFormed.snoc
    · apply Declaration.ContextWellFormed.snoc
      · apply Declaration.ContextWellFormed.snoc
        · exact .nil
        · exact .headType (.sort familyDomainLevel)
        · exact .sort (.succ familyDomainLevel)
      · exact familyType_hasType
      · exact .sort (.max familyDomainLevel (.succ familyCodomainLevel))
    · exact Presentation.HasType.var 1
    · exact .sort familyDomainLevel
  body := familyBody
  level := familyCodomainLevel
  bodyTyping := familyBody_hasType

def familyTemplates : TemplateSignature 1 := fun _ => familyTemplate

/-- The contextual code for the open family application `B x` in its own
declaration telescope. -/
def openFamilyCode : Code familyTemplates 3 :=
  .template 0 (ids (Head := Tower.Head))

theorem openFamilyCode_hasCode :
    HasCode familyContextABX openFamilyCode familyCodomainLevel := by
  exact .template (CtxMor.identity Tower.rules familyContextABX)

@[simp] theorem decode_openFamilyCode :
    decode openFamilyCode = familyBody := by
  change Presentation.subst (ids (Head := Tower.Head)) familyBody = familyBody
  exact subst_ids familyBody

/-- Negative control: the same template occurrence cannot be assigned a
different declared level merely by changing its expected annotation. -/
theorem openFamilyCode_not_at_domainLevel
    (distinct : familyDomainLevel ≠ familyCodomainLevel) :
    ¬ HasCode familyContextABX openFamilyCode familyDomainLevel := by
  intro formation
  exact distinct (template_level_unique formation)

/-! ## Axiom audit -/

#print axioms decode_subst
#print axioms Code.subst_comp
#print axioms HasCode.substitute
#print axioms HasCode.decode_hasType
#print axioms generated_hasCode_iff
#print axioms openFamilyCode_hasCode
#print axioms openFamilyCode_not_at_domainLevel

end Contextual
end RussellTarski
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
