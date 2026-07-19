/-
# Canonical forms for the simple erasure of indexed LF

The indexed LF profile is dependently typed, but hereditary substitution is
well-founded on the ordinary simple erasure of a cut type.  This module makes
that erasure explicit.  `Normal` is intrinsically beta-normal and eta-long:
function-shaped normal forms are lambdas, while neutral heads can appear as
normal forms only at atomic shapes.  Names are Nat-interned; de Bruijn indices
remain the binding waist used by `LF.Term` and MeTTaIL.

This layer contains no conversion rule.  Application spines have neutral
heads, and the only operation that can create a beta redex is hereditary
instantiation, which contracts it while constructing the result.

Its scope is the typed action skeleton after simple erasure.  It is not a
normalizer or authentication route for dependent DTTBench source witnesses.
-/

import Mettapedia.GSLT.LanguageDef.LF.Profiles

namespace Mettapedia.GSLT.LanguageDef.LFCanonical

/-- Simple erasure of an LF type, used as the hereditary-substitution measure. -/
inductive Shape where
  | atom : Nat → Shape
  | arrow : Shape → Shape → Shape
  deriving DecidableEq, Repr

namespace Shape

def size : Shape → Nat
  | .atom _ => 1
  | .arrow domain codomain => domain.size + codomain.size + 1

@[simp] theorem size_pos (shape : Shape) : 0 < shape.size := by
  cases shape <;> simp [size]

@[simp] theorem domain_size_lt (domain codomain : Shape) :
    domain.size < (Shape.arrow domain codomain).size := by
  simp only [Shape.size]
  omega

@[simp] theorem codomain_size_lt (domain codomain : Shape) :
    codomain.size < (Shape.arrow domain codomain).size := by
  simp only [Shape.size]
  omega

end Shape

/-- Typed neutral heads.  The Nat name space is shared by variables and
interned constants, but the constructors keep their roles distinct. -/
inductive Head : Shape → Type where
  | var (shape : Shape) (index : Nat) : Head shape
  | con (shape : Shape) (name : Nat) : Head shape
  deriving DecidableEq, Repr

mutual

/-- Beta-normal, eta-long terms indexed by their simple type erasure. -/
inductive Normal : Shape → Type where
  | lam (domain : Shape) {codomain : Shape} :
      Normal codomain → Normal (.arrow domain codomain)
  | atom {name : Nat} : Neutral (.atom name) → Normal (.atom name)

/-- A typed application spine from the head type to the result type. -/
inductive Spine : Shape → Shape → Type where
  | nil (shape : Shape) : Spine shape shape
  | cons {domain codomain result : Shape} :
      Normal domain → Spine codomain result →
      Spine (.arrow domain codomain) result

/-- A neutral head together with its fully typed application spine. -/
inductive Neutral : Shape → Type where
  | mk {headShape resultShape : Shape} :
      Head headShape → Spine headShape resultShape → Neutral resultShape

end

/-! ## A raw simple-erasure calculus and its declarative typing -/

/-- Raw terms used only to state the declarative correspondence theorem. -/
inductive Raw where
  | var : Shape → Nat → Raw
  | con : Shape → Nat → Raw
  | lam : Shape → Raw → Raw
  | app : Shape → Shape → Raw → Raw → Raw
  deriving DecidableEq, Repr

abbrev Signature := Nat → Option Shape
abbrev Context := List Shape

namespace Raw

/-- Declarative typing for the simple erasure.  There is deliberately no
conversion constructor. -/
inductive Deriv (signature : Signature) : Context → Raw → Shape → Prop where
  | var {context index shape} :
      context[index]? = some shape →
      Deriv signature context (.var shape index) shape
  | con {context name shape} :
      signature name = some shape →
      Deriv signature context (.con shape name) shape
  | lam {context domain body codomain} :
      Deriv signature (domain :: context) body codomain →
      Deriv signature context (.lam domain body) (.arrow domain codomain)
  | app {context fn argument domain codomain} :
      Deriv signature context fn (.arrow domain codomain) →
      Deriv signature context argument domain →
      Deriv signature context (.app domain codomain fn argument) codomain

end Raw

def Head.erase : {shape : Shape} → Head shape → Raw
  | _, .var headShape index => .var headShape index
  | _, .con headShape name => .con headShape name

mutual

def Normal.erase : {shape : Shape} → Normal shape → Raw
  | _, .lam domain body => .lam domain body.erase
  | .atom _, .atom neutral => neutral.erase

def Spine.erase : {headShape resultShape : Shape} →
    Spine headShape resultShape → Raw → Raw
  | _, _, .nil _, head => head
  | _, _, @Spine.cons domain codomain _ argument rest, head =>
      rest.erase (.app domain codomain head argument.erase)

def Neutral.erase : {shape : Shape} → Neutral shape → Raw
  | _, .mk head spine => spine.erase head.erase

end

/-! ## Canonical typing -/

/-- The three mutually dependent canonical judgments, reified as one index so
their derivations have one honest induction principle. -/
inductive Judgment where
  | normal (context : Context) {shape : Shape} (term : Normal shape)
  | spine (context : Context) {headShape resultShape : Shape}
      (arguments : Spine headShape resultShape)
  | neutral (context : Context) {shape : Shape} (term : Neutral shape)

/-- Bidirectional canonical typing.  The rules are syntax directed and contain
no conversion premise or conversion constructor. -/
inductive CanonicalDeriv (signature : Signature) : Judgment → Prop where
  | lam {context domain codomain} {body : Normal codomain} :
      CanonicalDeriv signature (.normal (domain :: context) body) →
      CanonicalDeriv signature
        (.normal context (Normal.lam domain body))
  | atom {context name} {neutral : Neutral (.atom name)} :
      CanonicalDeriv signature (.neutral context neutral) →
      CanonicalDeriv signature (.normal context (Normal.atom neutral))
  | spineNil {context shape} :
      CanonicalDeriv signature (.spine context (.nil shape))
  | spineCons {context domain codomain result}
      {argument : Normal domain} {rest : Spine codomain result} :
      CanonicalDeriv signature (.normal context argument) →
      CanonicalDeriv signature (.spine context rest) →
      CanonicalDeriv signature (.spine context (.cons argument rest))
  | neutralVar {context headShape resultShape index}
      {spine : Spine headShape resultShape} :
      context[index]? = some headShape →
      CanonicalDeriv signature (.spine context spine) →
      CanonicalDeriv signature
        (.neutral context (.mk (.var headShape index) spine))
  | neutralCon {context headShape resultShape name}
      {spine : Spine headShape resultShape} :
      signature name = some headShape →
      CanonicalDeriv signature (.spine context spine) →
      CanonicalDeriv signature
        (.neutral context (.mk (.con headShape name) spine))

/-- Declarative meaning of each canonical judgment. -/
def Judgment.Sound (signature : Signature) : Judgment → Prop
  | @Judgment.normal context shape term =>
      Raw.Deriv signature context term.erase shape
  | @Judgment.spine context headShape resultShape arguments =>
      ∀ head, Raw.Deriv signature context head headShape →
        Raw.Deriv signature context (arguments.erase head) resultShape
  | @Judgment.neutral context shape term =>
      Raw.Deriv signature context term.erase shape

/-- Canonical derivations correspond soundly to the raw declarative calculus. -/
theorem CanonicalDeriv.sound {signature : Signature} {judgment : Judgment}
    (derivation : CanonicalDeriv signature judgment) :
    judgment.Sound signature := by
  induction derivation with
  | lam _ ih => exact Raw.Deriv.lam ih
  | atom _ ih => exact ih
  | spineNil =>
      intro head hhead
      exact hhead
  | spineCons _ _ ihArgument ihRest =>
      intro head hhead
      exact ihRest _ (.app hhead ihArgument)
  | neutralVar hlookup _ ihSpine =>
      exact ihSpine _ (.var hlookup)
  | neutralCon hlookup _ ihSpine =>
      exact ihSpine _ (.con hlookup)

/-- Convenient normal-form checking proposition. -/
abbrev Checks (signature : Signature) (context : Context)
    {shape : Shape} (normal : Normal shape) : Prop :=
  CanonicalDeriv signature (.normal context normal)

/-- Convenient neutral-synthesis proposition. -/
abbrev SynthNeutral (signature : Signature) (context : Context)
    {shape : Shape} (neutral : Neutral shape) : Prop :=
  CanonicalDeriv signature (.neutral context neutral)

/-- Normal-form specialization of `CanonicalDeriv.sound`. -/
theorem Checks.sound {signature : Signature} {context : Context}
    {shape : Shape} {normal : Normal shape}
    (hchecks : Checks signature context normal) :
    Raw.Deriv signature context normal.erase shape :=
  CanonicalDeriv.sound hchecks

/-! ## Renaming and eta expansion -/

def liftRenaming (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => rename index + 1

def Head.rename (rename : Nat → Nat) : {shape : Shape} → Head shape → Head shape
  | _, .var shape index => .var shape (rename index)
  | _, .con shape name => .con shape name

mutual

def Normal.rename (rename : Nat → Nat) :
    {shape : Shape} → Normal shape → Normal shape
  | _, .lam domain body => .lam domain (body.rename (liftRenaming rename))
  | _, .atom neutral => .atom (neutral.rename rename)

def Spine.rename (rename : Nat → Nat) :
    {headShape resultShape : Shape} →
      Spine headShape resultShape → Spine headShape resultShape
  | _, _, .nil shape => .nil shape
  | _, _, .cons argument rest =>
      .cons (argument.rename rename) (rest.rename rename)

def Neutral.rename (rename : Nat → Nat) :
    {shape : Shape} → Neutral shape → Neutral shape
  | _, .mk head spine => .mk (head.rename rename) (spine.rename rename)

end

/-- Compose two typed spines. -/
def Spine.append {headShape middleShape resultShape : Shape} :
    Spine headShape middleShape → Spine middleShape resultShape →
      Spine headShape resultShape
  | .nil _, suffix => suffix
  | .cons argument rest, suffix => .cons argument (rest.append suffix)

/-- Append one argument to a typed neutral spine. -/
def Spine.snoc {headShape domain codomain : Shape}
    (spine : Spine headShape (.arrow domain codomain))
    (argument : Normal domain) : Spine headShape codomain :=
  spine.append (.cons argument (.nil codomain))

def Neutral.apply {domain codomain : Shape}
    (neutral : Neutral (.arrow domain codomain))
    (argument : Normal domain) : Neutral codomain := by
  cases neutral with
  | mk head spine => exact .mk head (spine.snoc argument)

/-- Eta expansion is structural recursion on the simple erasure. -/
def etaExpand : (shape : Shape) → Neutral shape → Normal shape
  | .atom _, neutral => .atom neutral
  | .arrow domain codomain, neutral =>
      .lam domain (etaExpand codomain
        ((neutral.rename Nat.succ).apply
          (etaExpand domain (.mk (.var domain 0) (.nil domain)))))
termination_by shape => shape.size
decreasing_by
  all_goals simp only [Shape.size]
  all_goals omega

/-- Canonical eta expansion of a variable at any simple shape. -/
def etaVariable (shape : Shape) (index : Nat) : Normal shape :=
  etaExpand shape (.mk (.var shape index) (.nil shape))

/-! ## Hereditary substitution

The following mutually recursive operation is ordered lexicographically by
the cut type's simple-erasure size and then by canonical syntax size.  The
extra phase bit accounts for the one transition from finding the substituted
head to consuming its already-substituted spine.  Every beta contraction then
recurses at a strict domain/codomain subshape of the cut type.
-/

mutual

def Normal.weight : {shape : Shape} → Normal shape → Nat
  | _, .lam _ body => body.weight + 1
  | _, .atom neutral => neutral.weight + 1

def Spine.weight : {headShape resultShape : Shape} →
    Spine headShape resultShape → Nat
  | _, _, .nil _ => 1
  | _, _, .cons argument rest => argument.weight + rest.weight + 1

def Neutral.weight : {shape : Shape} → Neutral shape → Nat
  | _, .mk _ spine => spine.weight + 1

end


def loweredIndex (target index : Nat) : Nat :=
  if target < index then index - 1 else index

mutual

/-- Hereditary substitution of one de Bruijn variable by a canonical term. -/
def hereditarySubst (cut : Shape) (target : Nat) (replacement : Normal cut) :
    {shape : Shape} → Normal shape → Normal shape
  | _, .lam domain body =>
      .lam domain (hereditarySubst cut (target + 1)
        (replacement.rename Nat.succ) body)
  | _, .atom neutral =>
      hereditaryNeutral cut target replacement neutral
termination_by shape term =>
  (cut.size, term.weight + 1)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Normal.weight]
  all_goals omega

/-- Substitute through every canonical argument of a neutral spine. -/
def hereditarySpine (cut : Shape) (target : Nat) (replacement : Normal cut) :
    {headShape resultShape : Shape} →
      Spine headShape resultShape → Spine headShape resultShape
  | _, _, .nil shape => .nil shape
  | _, _, .cons argument rest =>
      .cons (hereditarySubst cut target replacement argument)
        (hereditarySpine cut target replacement rest)
termination_by headShape resultShape spine =>
  (cut.size, spine.weight + 1)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Spine.weight]
  all_goals omega

/-- Substitute into an atomic neutral; replacing its head immediately consumes
the spine and contracts every beta redex exposed by that replacement. -/
def hereditaryNeutral (cut : Shape) (target : Nat) (replacement : Normal cut) :
    {name : Nat} → Neutral (.atom name) → Normal (.atom name)
  | _, .mk (.con headShape name) spine =>
      .atom (.mk (.con headShape name)
        (hereditarySpine cut target replacement spine))
  | _, .mk (.var headShape index) spine =>
      let substitutedSpine := hereditarySpine cut target replacement spine
      if _hindex : index = target then
        if hshape : headShape = cut then
          hereditaryInstantiate headShape
            (hshape ▸ replacement) substitutedSpine
        else
          .atom (.mk (.var headShape index) substitutedSpine)
      else
        .atom (.mk (.var headShape (loweredIndex target index))
          substitutedSpine)
termination_by name neutral =>
  (cut.size, neutral.weight + 1)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Neutral.weight]
  all_goals omega

/-- Consume a canonical application spine.  At function shape the canonical
function is necessarily a lambda, so the next step is hereditary substitution
at the strict domain subshape. -/
def hereditaryInstantiate (functionShape : Shape) :
    {resultShape : Shape} →
      Normal functionShape → Spine functionShape resultShape →
        Normal resultShape
  | _, function, .nil _ => function
  | _, .lam _ body, .cons argument rest =>
      hereditaryInstantiate _
        (hereditarySubst _ 0 argument body) rest
termination_by _ _ _ =>
  (functionShape.size, 0)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Shape.size]
  all_goals omega

end


/-- Substitution at the innermost binder. -/
def hereditarySubst0 {cut shape : Shape}
    (replacement : Normal cut) (body : Normal shape) : Normal shape :=
  hereditarySubst cut 0 replacement body

/-! ## Completeness of canonical typing with respect to erasure -/

mutual

/-- A declarative derivation of a canonical erasure reconstructs the normal
canonical derivation. -/
theorem Normal.complete {signature : Signature} {context : Context}
    {shape : Shape} :
    (normal : Normal shape) →
    Raw.Deriv signature context normal.erase shape →
    CanonicalDeriv signature (.normal context normal)
  | .lam domain body, derivation => by
      cases derivation with
      | lam hbody => exact .lam (body.complete hbody)
  | .atom neutral, derivation => .atom (neutral.complete derivation)
termination_by normal _ => normal.weight
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Normal.weight]
  all_goals omega

/-- Peeling a canonical spine from a declarative result recovers both the
head derivation and canonical checking of every argument. -/
theorem Spine.complete {signature : Signature} {context : Context}
    {headShape resultShape : Shape} :
    (spine : Spine headShape resultShape) →
    (head : Raw) →
    Raw.Deriv signature context (spine.erase head) resultShape →
    Raw.Deriv signature context head headShape ∧
      CanonicalDeriv signature (.spine context spine)
  | .nil _, _, derivation => ⟨derivation, .spineNil⟩
  | @Spine.cons domain codomain _ argument rest, head, derivation =>
      let ⟨happlication, hrest⟩ :=
        rest.complete (.app domain codomain head argument.erase) derivation
      match happlication with
      | .app hhead hargument =>
          ⟨hhead, .spineCons (argument.complete hargument) hrest⟩
termination_by spine _ _ => spine.weight
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Spine.weight]
  all_goals omega

/-- Declarative typing of a neutral erasure reconstructs head lookup and its
checked canonical spine. -/
theorem Neutral.complete {signature : Signature} {context : Context}
    {shape : Shape} :
    (neutral : Neutral shape) →
    Raw.Deriv signature context neutral.erase shape →
    CanonicalDeriv signature (.neutral context neutral)
  | .mk (.var headShape index) spine, derivation =>
      let ⟨hhead, hspine⟩ :=
        spine.complete (.var headShape index) derivation
      match hhead with
      | .var hlookup => .neutralVar hlookup hspine
  | .mk (.con headShape name) spine, derivation =>
      let ⟨hhead, hspine⟩ :=
        spine.complete (.con headShape name) derivation
      match hhead with
      | .con hlookup => .neutralCon hlookup hspine
termination_by neutral _ => neutral.weight
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Neutral.weight]
  all_goals omega
end

/-- T3 correspondence crown: canonical checking is equivalent to declarative
typing of the erased term, with no conversion rule on either side. -/
theorem canonicalDeriv_iff_rawDeriv {signature : Signature}
    {context : Context} {shape : Shape} {normal : Normal shape} :
    Checks signature context normal ↔
      Raw.Deriv signature context normal.erase shape := by
  constructor
  · exact Checks.sound
  · exact normal.complete

def fixtureAtom : Shape := .atom 0

def fixtureConstant (shape : Shape) (name : Nat) : Normal shape :=
  etaExpand shape (.mk (.con shape name) (.nil shape))

def fixtureIdentity : Normal (.arrow fixtureAtom fixtureAtom) :=
  .lam fixtureAtom (etaVariable fixtureAtom 0)

def fixtureAppliedVariable : Normal fixtureAtom :=
  .atom (.mk (.var (.arrow fixtureAtom fixtureAtom) 0)
    (.cons (fixtureConstant fixtureAtom 7) (.nil fixtureAtom)))

/-- `Eq_congrFun`-shape fixture: substituting an eta-long identity for an
applied function variable contracts the exposed beta redex immediately. -/
theorem hereditarySubst_congrFun_shape :
    hereditarySubst0 fixtureIdentity fixtureAppliedVariable =
      fixtureConstant fixtureAtom 7 := by
  simp [hereditarySubst0, fixtureIdentity, fixtureAppliedVariable,
    fixtureConstant, hereditarySubst, hereditaryNeutral, hereditarySpine,
    hereditaryInstantiate, etaVariable, etaExpand, fixtureAtom]

def fixtureElement : Shape := .atom 1
def fixtureProp : Shape := .atom 2
def fixturePredicate : Shape := .arrow fixtureElement fixtureProp
def fixtureSetFunctional : Shape := .arrow fixturePredicate fixtureProp

def fixtureSetFunctionalReplacement : Normal fixtureSetFunctional :=
  .lam fixturePredicate (fixtureConstant fixtureProp 11)

def fixtureSetFunctionalApplication : Normal fixtureProp :=
  .atom (.mk (.var fixtureSetFunctional 0)
    (.cons (fixtureConstant fixturePredicate 13) (.nil fixtureProp)))

/-- `sSup_inter_le`-shape fixture: hereditary substitution also contracts a
higher-order set-functional application and leaves an eta-long result. -/
theorem hereditarySubst_sSup_shape :
    hereditarySubst0 fixtureSetFunctionalReplacement
      fixtureSetFunctionalApplication = fixtureConstant fixtureProp 11 := by
  simp [hereditarySubst0, fixtureSetFunctionalReplacement,
    fixtureSetFunctionalApplication, fixtureConstant, hereditarySubst,
    hereditaryNeutral, hereditarySpine, hereditaryInstantiate,
    etaExpand, Neutral.apply, Neutral.rename, Spine.rename, Head.rename,
    Spine.snoc, Spine.append, Normal.rename, loweredIndex,
    fixtureSetFunctional, fixturePredicate, fixtureElement, fixtureProp]

/-- Positive fixture: an arrow neutral expands to a lambda-headed normal form. -/
example : ∃ body : Normal fixtureAtom,
    etaVariable (.arrow fixtureAtom fixtureAtom) 0 =
      Normal.lam fixtureAtom body := by
  refine ⟨Normal.atom (.mk (.var (.arrow fixtureAtom fixtureAtom) 1)
    (.cons (Normal.atom (.mk (.var fixtureAtom 0) (.nil fixtureAtom)))
      (.nil fixtureAtom))), ?_⟩
  simp [etaVariable, etaExpand, Neutral.apply, Neutral.rename,
    Spine.rename, Head.rename, Spine.snoc, Spine.append,
    fixtureAtom]

/-- Negative fixture: a bare function variable is declaratively typable but
cannot be the erasure of an eta-long function normal form. -/
theorem etaShort_variable_not_canonical (domain codomain : Shape) (index : Nat) :
    ¬ ∃ normal : Normal (.arrow domain codomain),
      normal.erase = .var (.arrow domain codomain) index := by
  intro hexists
  obtain ⟨normal, hnormal⟩ := hexists
  cases normal with
  | lam _ body => simp [Normal.erase] at hnormal

#print axioms Checks.sound
#print axioms CanonicalDeriv.sound
#print axioms canonicalDeriv_iff_rawDeriv
#print axioms hereditarySubst_congrFun_shape
#print axioms hereditarySubst_sSup_shape
#print axioms etaShort_variable_not_canonical

end Mettapedia.GSLT.LanguageDef.LFCanonical
