import Mettapedia.GSLT.Dedukti.PureTypeSystem

/-!
# The Cousineau–Dowek embedding of a pure type system

Source: D. Cousineau and G. Dowek, *Embedding pure type systems in the
lambda-Pi-calculus modulo*, TLCA 2007.  Conservativity in general: A. Assaf,
*Conservativity of embeddings in the lambda-Pi calculus modulo rewriting*,
TLCA 2015.

For a pure type system `P` the theory `cdTheory P` of the λΠ-calculus modulo
has, for each sort `s`, a type `U s` of codes and a decoding `e s : U s → Type`;
for each axiom `s1 : s2` a code `dot s1 : U s2`; for each rule `(s1, s2, s3)`
a code former `dotpi : Π X : U s1. (e s1 X → U s2) → U s3`; and the two
families of rewrite rules

    e s2 (dot s1)        ⟶  U s1
    e s3 (dotpi X Y)     ⟶  Π x : e s1 X. e s2 (Y x)

At the profile of the calculus of constructions these are the declarations of
`examples/coc.dk` in the Dedukti distribution, up to the names of the four
product codes.

`translate` is the translation of terms, `|t|` in the paper, as a fold over
the sort-annotated syntax of `PureTypeSystem`.  The translation of a type `A`
of sort `s` is `e s |A|`.

## What is proved

* `translate_sound` (Proposition 3 of the paper, Theorem 4.5 of Assaf): a
  sorted derivation of `P` translates to a derivation of the λΠ-calculus
  modulo `cdTheory P`.  No hypothesis on `P`.
* `translate_transGen`, `translate_conv`: a beta step of the source is a
  nonempty reduction of the target, hence conversion is preserved.
* `translate_acc` (Proposition 4): where the target terminates, so does the
  source.
* `backTranslate` (Definition 12), as the interpretation of each constant by a
  closed term of the pure type system: `U s` and `dot s` by the sort `s`,
  `e s` by the identity, `dotpi` by `λ a. λ b. Π x : a. b x`.  It preserves
  conversion (`backTranslate_conv`) and is a left inverse of the translation
  up to beta (`backTranslate_translate`).
* `translate_reflects`: if the translations of two terms are convertible in
  the target, the raw terms are beta convertible.  No hypothesis.

## What is modelled, and how it differs from the printed definitions

* The type translation uses the decoding at every sorted type.  The paper
  writes `U s'` for the translation of a sort `s'` as a type; here it is
  `e s (dot s')`, which reduces to `U s'` by the first rule
  (`conv_code`).  Assaf notes that the definition is determined only up to
  conversion.
* Proposition 1.2 of the paper says that a beta step is translated to a beta
  step.  The translation of a product contains its domain twice, so a step in
  a domain is two steps (`translate_transGen`); see
  `CousineauDowekMorphism` for the witness that it is not one.
* Proposition 11 says that the back translation is a right inverse.  It is one
  up to beta (`backTranslate_translate`): the back translation of the
  translation of `Π x : A. B` is `Π x : A. (λ x : A. B) x`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)

/-! ## The constants of the embedding -/

/-- The constants that the embedding declares. -/
inductive Symbol where
  /-- The type of codes of a sort. -/
  | univ : Srt → Symbol
  /-- The decoding of the codes of a sort. -/
  | decode : Srt → Symbol
  /-- The code of a sort. -/
  | code : Srt → Symbol
  /-- The code former of a product rule. -/
  | prod : ProductRule → Symbol
  deriving DecidableEq, Repr

namespace Symbol

/-- The name of a constant.  The first five are the names of
`examples/coc.dk`. -/
def name : Symbol → String
  | .univ .type => "Utype"
  | .univ .kind => "Ukind"
  | .decode .type => "etype"
  | .decode .kind => "ekind"
  | .code .type => "dottype"
  | .code .kind => "dotkind"
  | .prod ⟨.type, .type, .type⟩ => "dotpi_type_type_type"
  | .prod ⟨.type, .type, .kind⟩ => "dotpi_type_type_kind"
  | .prod ⟨.type, .kind, .type⟩ => "dotpi_type_kind_type"
  | .prod ⟨.type, .kind, .kind⟩ => "dotpi_type_kind_kind"
  | .prod ⟨.kind, .type, .type⟩ => "dotpi_kind_type_type"
  | .prod ⟨.kind, .type, .kind⟩ => "dotpi_kind_type_kind"
  | .prod ⟨.kind, .kind, .type⟩ => "dotpi_kind_kind_type"
  | .prod ⟨.kind, .kind, .kind⟩ => "dotpi_kind_kind_kind"

/-- Every constant. -/
def all : List Symbol :=
  [.univ .type, .univ .kind, .decode .type, .decode .kind, .code .type, .code .kind,
    .prod ⟨.type, .type, .type⟩, .prod ⟨.type, .type, .kind⟩, .prod ⟨.type, .kind, .type⟩,
    .prod ⟨.type, .kind, .kind⟩, .prod ⟨.kind, .type, .type⟩, .prod ⟨.kind, .type, .kind⟩,
    .prod ⟨.kind, .kind, .type⟩, .prod ⟨.kind, .kind, .kind⟩]

/-- The constant with a given name, if there is one. -/
def ofName (name : String) : Option Symbol :=
  all.find? fun symbol => symbol.name == name

theorem ofName_name (symbol : Symbol) : ofName symbol.name = some symbol := by
  cases symbol with
  | univ level => cases level <;> decide
  | decode level => cases level <;> decide
  | code level => cases level <;> decide
  | prod rule =>
      obtain ⟨domain, codomain, result⟩ := rule
      cases domain <;> cases codomain <;> cases result <;> decide

theorem name_injective : Function.Injective name := by
  intro first second same
  have found := ofName_name first
  rw [same, ofName_name] at found
  exact (Option.some.inj found).symm

end Symbol

/-- The type of codes of a sort. -/
def codeType (level : Srt) : Term := .con (Symbol.univ level).name

/-- The type that a code denotes. -/
def El (level : Srt) (term : Term) : Term := .app (.con (Symbol.decode level).name) term

/-- The code of a sort. -/
def sortCode (level : Srt) : Term := .con (Symbol.code level).name

/-- The code of a product. -/
def prodCode (rule : ProductRule) (domain family : Term) : Term :=
  .app (.app (.con (Symbol.prod rule).name) domain) family

/-- The declared type of a constant. -/
def Symbol.declaredType (profile : Profile) : Symbol → Option Term
  | .univ _ => some (.srt .type)
  | .decode level => some (.pi (codeType level) (.srt .type))
  | .code level => (profile.sortAxiom level).map codeType
  | .prod rule =>
      if rule ∈ profile.products then
        some (.pi (codeType rule.domain)
          (.pi (.pi (El rule.domain (.var 0)) (codeType rule.codomain)) (codeType rule.result)))
      else none

/-- The rule `e s2 (dot s1) ⟶ U s1`. -/
def codeRule (source target : Srt) : RewriteRule :=
  ⟨El target (sortCode source), codeType source⟩

/-- The rule `e s3 (dotpi X Y) ⟶ Π x : e s1 X. e s2 (Y x)`.  The pattern
variables are `X`, the variable 1, and `Y`, the variable 0. -/
def prodRule (rule : ProductRule) : RewriteRule :=
  ⟨El rule.result (prodCode rule (.var 1) (.var 0)),
    .pi (El rule.domain (.var 1)) (El rule.codomain (.app (.var 1) (.var 0)))⟩

/-- The universe-reduction rules of a pure type system. -/
inductive UniverseRule (profile : Profile) : RewriteRule → Prop where
  | code {source target : Srt} :
      profile.sortAxiom source = some target → UniverseRule profile (codeRule source target)
  | prod {rule : ProductRule} :
      rule ∈ profile.products → UniverseRule profile (prodRule rule)

/-- **The theory of the embedding of a pure type system.** -/
def cdTheory (profile : Profile) : Theory where
  constType := fun name => (Symbol.ofName name).bind (Symbol.declaredType profile)
  body := fun _ => none
  rule := UniverseRule profile

variable {profile : Profile}

theorem cdTheory_headed (profile : Profile) : (cdTheory profile).Headed := by
  intro rule member
  cases member with
  | code _ => exact ⟨_, rfl⟩
  | prod _ => exact ⟨_, rfl⟩

theorem constType_symbol (profile : Profile) (symbol : Symbol) :
    (cdTheory profile).constType symbol.name = Symbol.declaredType profile symbol := by
  simp [cdTheory, Symbol.ofName_name]

/-! ## Instances of the two rules -/

theorem inst_codeRule_lhs (source target : Srt) (assignment : Nat → Term) :
    inst assignment (codeRule source target).lhs = El target (sortCode source) := rfl

theorem inst_codeRule_rhs (source target : Srt) (assignment : Nat → Term) :
    inst assignment (codeRule source target).rhs = codeType source := rfl

theorem inst_prodRule_lhs (rule : ProductRule) (assignment : Nat → Term) :
    inst assignment (prodRule rule).lhs =
      El rule.result (prodCode rule (assignment 1) (assignment 0)) := by
  simp [prodRule, El, prodCode, inst, instantiate, lift_zero]

theorem inst_prodRule_rhs (rule : ProductRule) (assignment : Nat → Term) :
    inst assignment (prodRule rule).rhs =
      .pi (El rule.domain (assignment 1))
        (El rule.codomain (.app (lift 1 0 (assignment 0)) (.var 0))) := by
  simp [prodRule, El, inst, instantiate, lift_zero]

/-- The first rule, as a conversion. -/
theorem conv_code {source target : Srt} (axiomHolds : profile.sortAxiom source = some target) :
    Conv (cdTheory profile) (El target (sortCode source)) (codeType source) :=
  Conv.rule (theory := cdTheory profile) (rule := codeRule source target) (.code axiomHolds)
    fun _ => .srt .type

/-- The second rule applied to an abstraction, followed by the beta step it
creates: the decoding of the code of a product is the product of the
decodings (Proposition 2 of the paper). -/
theorem conv_prod {rule : ProductRule} (member : rule ∈ profile.products)
    (domain annotation body : Term) :
    Conv (cdTheory profile) (El rule.result (prodCode rule domain (.lam annotation body)))
      (.pi (El rule.domain domain) (El rule.codomain body)) := by
  have instance_ := Conv.rule (theory := cdTheory profile) (rule := prodRule rule) (.prod member)
    fun index => if index = 0 then .lam annotation body else domain
  rw [inst_prodRule_lhs, inst_prodRule_rhs] at instance_
  have beta := Conv.beta (theory := cdTheory profile) (lift 1 0 annotation) (lift 1 1 body) (.var 0)
  rw [subst0_var_lift] at beta
  refine .trans _ _ _ instance_ (Conv.pi (.refl _) (Conv.app (.refl _) ?_))
  simpa [lift] using beta

/-! ## The typing of the constants -/

theorem type_codeType (profile : Profile) (context : Ctx) (level : Srt) :
    LambdaPiModulo (cdTheory profile) context (codeType level) (.srt .type) :=
  .con (constType_symbol profile (.univ level))

theorem type_El {context : Ctx} {level : Srt} {term : Term}
    (typed : LambdaPiModulo (cdTheory profile) context term (codeType level)) :
    LambdaPiModulo (cdTheory profile) context (El level term) (.srt .type) := by
  have decoder : LambdaPiModulo (cdTheory profile) context (.con (Symbol.decode level).name)
      (.pi (codeType level) (.srt .type)) := .con (constType_symbol profile (.decode level))
  exact .app decoder typed

theorem type_sortCode (context : Ctx) {source target : Srt}
    (axiomHolds : profile.sortAxiom source = some target) :
    LambdaPiModulo (cdTheory profile) context (sortCode source) (codeType target) :=
  .con (by rw [constType_symbol]; simp [Symbol.declaredType, axiomHolds])

theorem arrow_rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.basic.products := by decide

theorem type_prodCode {context : Ctx} {rule : ProductRule} (member : rule ∈ profile.products)
    {domain body : Term}
    (domainTyped : LambdaPiModulo (cdTheory profile) context domain (codeType rule.domain))
    (bodyTyped : LambdaPiModulo (cdTheory profile) (El rule.domain domain :: context) body
      (codeType rule.codomain)) :
    LambdaPiModulo (cdTheory profile) context
      (prodCode rule domain (.lam (El rule.domain domain) body)) (codeType rule.result) := by
  have constant : LambdaPiModulo (cdTheory profile) context (.con (Symbol.prod rule).name)
      (.pi (codeType rule.domain)
        (.pi (.pi (El rule.domain (.var 0)) (codeType rule.codomain)) (codeType rule.result))) :=
    .con (by rw [constType_symbol]; simp [Symbol.declaredType, member])
  have first := HasType.app constant domainTyped
  have shape : subst0 domain
      (.pi (.pi (El rule.domain (.var 0)) (codeType rule.codomain)) (codeType rule.result)) =
      .pi (.pi (El rule.domain domain) (codeType rule.codomain)) (codeType rule.result) := by
    simp [subst0, subst, El, codeType]
  rw [shape] at first
  have family : LambdaPiModulo (cdTheory profile) context (.lam (El rule.domain domain) body)
      (.pi (El rule.domain domain) (codeType rule.codomain)) :=
    .lam (type_El domainTyped) (type_codeType profile _ _) arrow_rule bodyTyped
  exact .app first family

/-! ## The translation -/

/-- **The translation of terms**, as a fold over the annotated syntax. -/
def translate : PTerm → Term
  | .var index => .var index
  | .sort level => sortCode level
  | .pi rule domain body =>
      prodCode rule (translate domain) (.lam (El rule.domain (translate domain)) (translate body))
  | .lam level domain body => .lam (El level (translate domain)) (translate body)
  | .app function argument => .app (translate function) (translate argument)

theorem translate_lift (term : PTerm) :
    ∀ amount cutoff : Nat, translate (term.lift amount cutoff) = lift amount cutoff (translate term) := by
  induction term with
  | var index => intro amount cutoff; rfl
  | sort level => intro amount cutoff; rfl
  | pi rule domain body ihDomain ihBody =>
      intro amount cutoff
      simp [PTerm.lift, translate, lift, prodCode, El, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      intro amount cutoff
      simp [PTerm.lift, translate, lift, El, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff
      simp [PTerm.lift, translate, lift, ihFunction, ihArgument]

theorem translate_subst (term : PTerm) :
    ∀ (target : Nat) (replacement : PTerm),
      translate (PTerm.subst target replacement term) =
        subst target (translate replacement) (translate term) := by
  induction term with
  | var index =>
      intro target replacement
      by_cases same : index = target
      · simp [PTerm.subst, translate, subst, same]
      · by_cases above : target < index
        · simp [PTerm.subst, translate, subst, same, above]
        · simp [PTerm.subst, translate, subst, same, above]
  | sort level => intro target replacement; rfl
  | pi rule domain body ihDomain ihBody =>
      intro target replacement
      simp [PTerm.subst, translate, subst, prodCode, El, ihDomain, ihBody, translate_lift]
  | lam level domain body ihDomain ihBody =>
      intro target replacement
      simp [PTerm.subst, translate, subst, El, ihDomain, ihBody, translate_lift]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [PTerm.subst, translate, subst, ihFunction, ihArgument]

theorem translate_subst0 (argument body : PTerm) :
    translate (PTerm.subst0 argument body) = subst0 (translate argument) (translate body) :=
  translate_subst body 0 argument

/-! ## Reduction is preserved -/

theorem transGen_plug {theory : Theory} (context : Context) {source target : Term}
    (reduces : Relation.TransGen (Step theory) source target) :
    Relation.TransGen (Step theory) (context.plug source) (context.plug target) := by
  induction reduces with
  | single step => exact .single (step.plug context)
  | tail _ step ih => exact ih.tail (step.plug context)

theorem conv_of_transGen {theory : Theory} {source target : Term}
    (reduces : Relation.TransGen (Step theory) source target) : Conv theory source target := by
  induction reduces with
  | single step => exact .rel _ _ step
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- **A beta step of the source is a nonempty reduction of the target.**  A
step in the domain of a product is two steps: the translation holds the
domain twice. -/
theorem translate_transGen (profile : Profile) {source target : PTerm}
    (step : PTerm.Step source target) :
    Relation.TransGen (Step (cdTheory profile)) (translate source) (translate target) := by
  induction step with
  | beta level domain body argument =>
      rw [translate_subst0]
      exact .single (Step.root (.beta _ _ _))
  | @piDomain rule domain domain' body _ ih =>
      have first := transGen_plug
        (.appFunction (.appArgument (.con (Symbol.prod rule).name) .hole)
          (.lam (El rule.domain (translate domain)) (translate body))) ih
      have second := transGen_plug
        (.appArgument (.app (.con (Symbol.prod rule).name) (translate domain'))
          (.lamDomain (.appArgument (.con (Symbol.decode rule.domain).name) .hole)
            (translate body))) ih
      exact first.trans second
  | @piBody rule domain body body' _ ih =>
      exact transGen_plug
        (.appArgument (.app (.con (Symbol.prod rule).name) (translate domain))
          (.lamBody (El rule.domain (translate domain)) .hole)) ih
  | @lamDomain level domain domain' body _ ih =>
      exact transGen_plug
        (.lamDomain (.appArgument (.con (Symbol.decode level).name) .hole) (translate body)) ih
  | lamBody _ ih => exact transGen_plug (.lamBody _ .hole) ih
  | appFunction _ ih => exact transGen_plug (.appFunction .hole _) ih
  | appArgument _ ih => exact transGen_plug (.appArgument _ .hole) ih

/-- **Conversion is preserved.** -/
theorem translate_conv (profile : Profile) {source target : PTerm}
    (convertible : PTerm.Conv source target) :
    Conv (cdTheory profile) (translate source) (translate target) := by
  induction convertible with
  | rel _ _ step => exact conv_of_transGen (translate_transGen profile step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

theorem acc_transGen {α : Type} {relation : α → α → Prop} {element : α}
    (accessible : Acc relation element) : Acc (Relation.TransGen relation) element := by
  induction accessible with
  | intro element _ ih =>
      refine ⟨element, fun earlier related => ?_⟩
      cases related with
      | single step => exact ih earlier step
      | tail reaches step => exact (ih _ step).inv reaches

/-- **Where the target terminates, the source terminates** (Proposition 4 of
the paper), at each term. -/
theorem translate_acc (profile : Profile) {term : PTerm}
    (terminates : Acc (fun next term => Step (cdTheory profile) term next) (translate term)) :
    Acc (fun next term => PTerm.Step term next) term := by
  have lifted := acc_transGen terminates
  have pulled := InvImage.accessible translate lifted
  exact Subrelation.accessible
    (fun step => Relation.transGen_swap.mpr (translate_transGen profile step)) pulled

/-! ## Soundness -/

/-- The translation of a context. -/
def translateCtx (context : SortedCtx) : Ctx :=
  context.map fun entry => El entry.2 (translate entry.1)

/-- The translation of a judgment: a term and its type. -/
def Judgment.image : Judgment → Term × Term
  | .type subject level => (translate subject, codeType level)
  | .term subject classifier level => (translate subject, El level (translate classifier))

theorem ctxLookup_translateCtx {context : SortedCtx} {index : Nat} {type : PTerm} {level : Srt}
    (found : lookupSorted context index = some (type, level)) :
    ctxLookup (translateCtx context) index = some (El level (translate type)) := by
  rw [ctxLookup_eq_getElem?]
  unfold lookupSorted at found
  unfold translateCtx
  rw [List.getElem?_map]
  cases entry : context[index]? with
  | none => rw [entry] at found; cases found
  | some value =>
      rw [entry] at found
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      simp [translate_lift, El, lift]

/-- **Soundness of the embedding**: a derivation of the pure type system
translates to a derivation of the λΠ-calculus modulo its theory. -/
theorem translate_sound {context : SortedCtx} {judgment : Judgment}
    (derivation : Derives profile context judgment) :
    LambdaPiModulo (cdTheory profile) (translateCtx context) judgment.image.1 judgment.image.2 := by
  induction derivation with
  | sort axiomHolds => exact type_sortCode _ axiomHolds
  | pi _ _ member ihDomain ihBody => exact type_prodCode member ihDomain ihBody
  | @ofTerm context subject level above _ axiomHolds ih =>
      exact .conv ih (conv_code axiomHolds) (type_codeType profile _ level)
  | toTerm _ axiomHolds ih =>
      exact .conv ih (.symm _ _ (conv_code axiomHolds)) (type_El (type_sortCode _ axiomHolds))
  | var found => exact .var (ctxLookup_translateCtx found)
  | @lam context domain body bodyType domainSort codomainSort resultSort _ _ member _
      ihDomain ihBodyType ihBody =>
      have product := type_prodCode member ihDomain ihBodyType
      have abstraction : LambdaPiModulo (cdTheory profile) (translateCtx context)
          (.lam (El domainSort (translate domain)) (translate body))
          (.pi (El domainSort (translate domain)) (El codomainSort (translate bodyType))) :=
        .lam (type_El ihDomain) (type_El ihBodyType) arrow_rule ihBody
      exact .conv abstraction (.symm _ _ (conv_prod member _ _ _)) (type_El product)
  | @app context function argument domain bodyType domainSort codomainSort resultSort _ _ member
      _ _ ihDomain ihBodyType ihFunction ihArgument =>
      have product : LambdaPiModulo (cdTheory profile) (translateCtx context)
          (.pi (El domainSort (translate domain)) (El codomainSort (translate bodyType)))
          (.srt .type) :=
        .pi (type_El ihDomain) (type_El ihBodyType) arrow_rule
      have function' := HasType.conv ihFunction (conv_prod member _ _ _) product
      have applied := HasType.app function' ihArgument
      simp only [Judgment.image, translate_subst0]
      exact applied
  | conv _ convertible _ ihTerm ihTarget =>
      exact .conv ihTerm (Conv.app (.refl _) (translate_conv profile convertible)) (type_El ihTarget)

/-! ## The back translation -/

/-- The meaning of `dotpi` in the pure type system: `λ a. λ b. Π x : a. b x`. -/
def productCombinator (rule : ProductRule) : Term :=
  .lam (.srt rule.domain)
    (.lam (.pi (.var 0) (.srt rule.codomain)) (.pi (.var 1) (.app (.var 1) (.var 0))))

/-- The meaning of each constant of the embedding as a closed term of the
pure type system. -/
def backMeaning (name : String) : Term :=
  match Symbol.ofName name with
  | some (.univ level) => .srt level
  | some (.decode level) => .lam (.srt level) (.var 0)
  | some (.code level) => .srt level
  | some (.prod rule) => productCombinator rule
  | none => .con name

theorem backMeaning_closed (name : String) : Closed (backMeaning name) := by
  unfold backMeaning
  split
  · exact .srt
  · exact .lam .srt (.var (by omega))
  · exact .srt
  · exact .lam .srt (.lam (.pi (.var (by omega)) .srt)
      (.pi (.var (by omega)) (.app (.var (by omega)) (.var (by omega)))))
  · exact .con

/-- **The back translation**, as an interpretation of constants. -/
def back : Interpretation := ⟨backMeaning, backMeaning_closed⟩

/-- The back translation of a term. -/
abbrev backTranslate (term : Term) : Term := back.apply term

@[simp] theorem backTranslate_var (index : Nat) : backTranslate (.var index) = .var index := rfl

@[simp] theorem backTranslate_app (function argument : Term) :
    backTranslate (.app function argument) = .app (backTranslate function) (backTranslate argument) :=
  rfl

@[simp] theorem backTranslate_lam (domain body : Term) :
    backTranslate (.lam domain body) = .lam (backTranslate domain) (backTranslate body) := rfl

@[simp] theorem backTranslate_pi (domain body : Term) :
    backTranslate (.pi domain body) = .pi (backTranslate domain) (backTranslate body) := rfl

theorem backTranslate_symbol (symbol : Symbol) :
    backTranslate (.con symbol.name) = backMeaning symbol.name := rfl

@[simp] theorem backTranslate_codeType (level : Srt) : backTranslate (codeType level) = .srt level := by
  simp [codeType, backTranslate_symbol, backMeaning, Symbol.ofName_name]

@[simp] theorem backTranslate_sortCode (level : Srt) : backTranslate (sortCode level) = .srt level := by
  simp [sortCode, backTranslate_symbol, backMeaning, Symbol.ofName_name]

@[simp] theorem backTranslate_El (level : Srt) (term : Term) :
    backTranslate (El level term) = .app (.lam (.srt level) (.var 0)) (backTranslate term) := by
  simp [El, backTranslate_symbol, backMeaning, Symbol.ofName_name]

@[simp] theorem backTranslate_prodCode (rule : ProductRule) (domain family : Term) :
    backTranslate (prodCode rule domain family) =
      .app (.app (productCombinator rule) (backTranslate domain)) (backTranslate family) := by
  simp [prodCode, backTranslate_symbol, backMeaning, Symbol.ofName_name]

theorem backTranslate_lift (term : Term) (amount cutoff : Nat) :
    backTranslate (lift amount cutoff term) = lift amount cutoff (backTranslate term) :=
  back.apply_lift term amount cutoff

/-- The identity applied to a term is convertible to the term. -/
theorem conv_identity {theory : Theory} (level : Srt) (term : Term) :
    Conv theory (.app (.lam (.srt level) (.var 0)) term) term := by
  have beta := Conv.beta (theory := theory) (.srt level) (.var 0) term
  have same : subst0 term (.var 0) = term := by simp [subst0, subst]
  rwa [same] at beta

/-- The meaning of `dotpi`, applied: `(λ a. λ b. Π x : a. b x) A B ≡ Π x : A. B x`. -/
theorem conv_productCombinator {theory : Theory} (rule : ProductRule) (domain family : Term) :
    Conv theory (.app (.app (productCombinator rule) domain) family)
      (.pi domain (.app (lift 1 0 family) (.var 0))) := by
  have first := Conv.beta (theory := theory) (.srt rule.domain)
    (.lam (.pi (.var 0) (.srt rule.codomain)) (.pi (.var 1) (.app (.var 1) (.var 0)))) domain
  have firstShape : subst0 domain
      (.lam (.pi (.var 0) (.srt rule.codomain)) (.pi (.var 1) (.app (.var 1) (.var 0)))) =
      .lam (.pi domain (.srt rule.codomain)) (.pi (lift 1 0 domain) (.app (.var 1) (.var 0))) := by
    simp [subst0, subst]
  rw [firstShape] at first
  have second := Conv.beta (theory := theory) (.pi domain (.srt rule.codomain))
    (.pi (lift 1 0 domain) (.app (.var 1) (.var 0))) family
  have secondShape : subst0 family (.pi (lift 1 0 domain) (.app (.var 1) (.var 0))) =
      .pi domain (.app (lift 1 0 family) (.var 0)) := by
    simp [subst0, subst, subst_lift_cancel]
  rw [secondShape] at second
  exact .trans _ _ _ (Conv.app first (.refl _)) second

/-- **The back translation meets the obligation on rules**: both
universe-reduction rules become beta conversions of the pure type system. -/
theorem back_respects (profile : Profile) : back.Respects (cdTheory profile) Theory.empty where
  body := fun _ _ defined => by cases defined
  rule := fun rule member assignment => by
    cases member with
    | @code source target axiomHolds =>
        have left : back.apply (inst assignment (codeRule source target).lhs) =
            .app (.lam (.srt target) (.var 0)) (.srt source) := by
          rw [inst_codeRule_lhs]
          simp
        have right : back.apply (inst assignment (codeRule source target).rhs) = .srt source := by
          rw [inst_codeRule_rhs]
          simp
        rw [left, right]
        exact conv_identity _ _
    | @prod rule member =>
        have left : back.apply (inst assignment (prodRule rule).lhs) =
            .app (.lam (.srt rule.result) (.var 0))
              (.app (.app (productCombinator rule) (backTranslate (assignment 1)))
                (backTranslate (assignment 0))) := by
          rw [inst_prodRule_lhs]
          simp
        have right : back.apply (inst assignment (prodRule rule).rhs) =
            .pi (.app (.lam (.srt rule.domain) (.var 0)) (backTranslate (assignment 1)))
              (.app (.lam (.srt rule.codomain) (.var 0))
                (.app (lift 1 0 (backTranslate (assignment 0))) (.var 0))) := by
          rw [inst_prodRule_rhs]
          simp [backTranslate_lift]
        rw [left, right]
        refine .trans _ _ _ (conv_identity _ _) ?_
        refine .trans _ _ _ (conv_productCombinator rule _ _) ?_
        exact .symm _ _ (Conv.pi (conv_identity _ _) (conv_identity _ _))

/-- **The back translation preserves conversion.** -/
theorem backTranslate_conv (profile : Profile) {first second : Term}
    (convertible : Conv (cdTheory profile) first second) :
    Conv Theory.empty (backTranslate first) (backTranslate second) :=
  (back_respects profile).conv convertible

/-- **The back translation is a left inverse of the translation, up to
beta.** -/
theorem backTranslate_translate (term : PTerm) :
    Conv Theory.empty (backTranslate (translate term)) term.erase := by
  induction term with
  | var index => exact .refl _
  | sort level => exact Conv.of_eq (backTranslate_sortCode level)
  | pi rule domain body ihDomain ihBody =>
      have shape : backTranslate (translate (.pi rule domain body)) =
          .app (.app (productCombinator rule) (backTranslate (translate domain)))
            (.lam (.app (.lam (.srt rule.domain) (.var 0)) (backTranslate (translate domain)))
              (backTranslate (translate body))) := by
        simp [translate]
      rw [shape]
      refine .trans _ _ _ (conv_productCombinator rule _ _) ?_
      refine Conv.pi ihDomain ?_
      have beta := Conv.beta (theory := Theory.empty)
        (lift 1 0 (.app (.lam (.srt rule.domain) (.var 0)) (backTranslate (translate domain))))
        (lift 1 1 (backTranslate (translate body))) (.var 0)
      rw [subst0_var_lift] at beta
      exact .trans _ _ _ (by simpa [lift] using beta) ihBody
  | lam level domain body ihDomain ihBody =>
      have shape : backTranslate (translate (.lam level domain body)) =
          .lam (.app (.lam (.srt level) (.var 0)) (backTranslate (translate domain)))
            (backTranslate (translate body)) := by
        simp [translate]
      rw [shape]
      exact Conv.lam (.trans _ _ _ (conv_identity _ _) ihDomain) ihBody
  | app function argument ihFunction ihArgument => exact Conv.app ihFunction ihArgument

/-- **The translation reflects conversion**, up to the erasure of the
annotations: if two translations are convertible in the theory of the
embedding, the raw terms are beta convertible. -/
theorem translate_reflects (profile : Profile) {first second : PTerm}
    (convertible : Conv (cdTheory profile) (translate first) (translate second)) :
    Conv Theory.empty first.erase second.erase :=
  .trans _ _ _ (.symm _ _ (backTranslate_translate first))
    (.trans _ _ _ (backTranslate_conv profile convertible) (backTranslate_translate second))

#print axioms Symbol.ofName_name
#print axioms conv_prod
#print axioms translate_subst
#print axioms translate_transGen
#print axioms translate_acc
#print axioms translate_sound
#print axioms back_respects
#print axioms backTranslate_translate
#print axioms translate_reflects

end Mettapedia.GSLT.Dedukti
