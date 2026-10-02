import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# The annotated declarative judgment

The typing and typed-equality judgment of the annotated calculus, over the
universe presentation of a rule package `R` (its heads, universes, joins,
cumulativity and head equality). What the annotations change is the
declarations: an annotated package (`ChurchRules R`) declares every constant at
an annotated type and computes by annotated root steps, and its declared types
and root steps erase to those of `R`.

The rules are those of `Derivable`, with three changes where abstractions carry
their domain:

* `lamIntro` types `λ (x : A). b` at `Π (x : A). B`, the domain being the
  annotation, whose formation is a premise of its own;
* `lamCong` relates abstractions whose domains are equal types. With
  annotations in the syntax this is forced: substituting two equal terms into
  an abstraction substitutes them into its domain too (`CDerivable.functional`);
* `betaPi` contracts `(λ (x : A). b) a`.

Every annotated rule erases to a rule of `Derivable` (`CDerivable.erase`), so
annotated derivations erase to derivations of the rule package.

**Premises of root steps.** A package may attach to each of its root steps a list
of premises, typings and typed equalities in the context of the step
(`CRootComputation.requires`), and the rule for root steps (`CDerivable.root`)
asks for a derivation of each. This is the form of a computation rule whose
premises type the arguments of its redex: `rec P z s zero ≡ z` under `P`, `z` and
`s` typed. Such premises are what a model can use: an induction over a derivation
has a hypothesis for each premise of the rule, and has none for the typings of the
arguments of a redex that inversion recovers from the typing of the redex. By
default a step requires no premises (`ChurchRules.PremiseFree`), and its rule is
then `CDerivable.rootFree`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-- A premise of a root step, in the context of the step: a typing or a typed
equality. -/
inductive CPremise (Head : Type) (n : Nat) : Type where
  | typing (term type : CTm Head n)
  | equality (left right type : CTm Head n)

/-- Renaming of a premise. -/
def CPremise.rename {n m : Nat} (ρ : Ren n m) : CPremise Head n → CPremise Head m
  | .typing t T => .typing (t.rename ρ) (T.rename ρ)
  | .equality a b T => .equality (a.rename ρ) (b.rename ρ) (T.rename ρ)

/-- Substitution into a premise. -/
def CPremise.subst {n m : Nat} (σ : CSub Head n m) : CPremise Head n → CPremise Head m
  | .typing t T => .typing (t.subst σ) (T.subst σ)
  | .equality a b T => .equality (a.subst σ) (b.subst σ) (T.subst σ)

/-- Declaration-specific root computation of annotated terms, stable under
renaming and substitution, with the premises its steps require.

`requires l r premises`: the judgment admits the step from `l` to `r` under the
typings and equalities `premises`, read in the context of the step
(`CDerivable.root`). The premises of a step rename and substitute with it. By
default a step requires no premises. -/
structure CRootComputation (Head : Type) where
  step : {n : Nat} → CTm Head n → CTm Head n → Prop
  rename : ∀ {n m : Nat} (ρ : Ren n m) {l r : CTm Head n}, step l r →
    step (l.rename ρ) (r.rename ρ)
  substitute : ∀ {n m : Nat} (σ : CSub Head n m) {l r : CTm Head n}, step l r →
    step (l.subst σ) (r.subst σ)
  requires : {n : Nat} → CTm Head n → CTm Head n → List (CPremise Head n) → Prop :=
    fun _ _ premises => premises = []
  requires_rename : ∀ {n m : Nat} (ρ : Ren n m) {l r : CTm Head n}
      {premises : List (CPremise Head n)}, requires l r premises →
      requires (l.rename ρ) (r.rename ρ) (premises.map (CPremise.rename ρ)) := by
    intro _ _ _ _ _ _ none
    subst none
    rfl
  requires_substitute : ∀ {n m : Nat} (σ : CSub Head n m) {l r : CTm Head n}
      {premises : List (CPremise Head n)}, requires l r premises →
      requires (l.subst σ) (r.subst σ) (premises.map (CPremise.subst σ)) := by
    intro _ _ _ _ _ _ none
    subst none
    rfl

/-- No root computation. -/
def CRootComputation.empty : CRootComputation Head where
  step := fun _ _ => False
  rename := fun _ _ _ impossible => impossible.elim
  substitute := fun _ _ _ impossible => impossible.elim

/-- An annotated counterpart of a rule package: annotated declared types and
annotated root steps, which erase to the package's. -/
structure ChurchRules (R : Rules Head) where
  constantType : DeclName → Option (CTm Head 0)
  computation : CRootComputation Head
  erase_constantType : ∀ name, (constantType name).map CTm.erase = R.constantType name
  erase_step : ∀ {n : Nat} {l r : CTm Head n}, computation.step l r →
    R.computation.step l.erase r.erase

/-- The annotation of a rule package without declarations: no annotated root
steps. -/
def ChurchRules.empty (R : Rules Head) (noConstants : ∀ name, R.constantType name = none) :
    ChurchRules R where
  constantType := fun _ => none
  computation := .empty
  erase_constantType := fun name => (noConstants name).symm
  erase_step := fun impossible => impossible.elim

/-- The three forms of annotated judgment. -/
inductive CStatement (Head : Type) : Type where
  | typing {n : Nat} (context : CCtx Head n) (term type : CTm Head n)
  | equality {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
  | sub {n : Nat} (context : CCtx Head n) (lower upper : CTm Head n)

/-- The statement a premise makes in a context. -/
def CPremise.statement {n : Nat} (Γ : CCtx Head n) : CPremise Head n → CStatement Head
  | .typing t T => .typing Γ t T
  | .equality a b T => .equality Γ a b T

variable {R : Rules Head}

/-- Derivable annotated typing, typed-equality and subtyping statements. -/
inductive CDerivable (P : ChurchRules R) : CStatement Head → Prop
  -- Typing
  | headType {n : Nat} {Γ : CCtx Head n} {h u : Head} :
      R.headTyping h u → CDerivable P (.typing Γ (.head h) (.head u))
  | var {n : Nat} {Γ : CCtx Head n} (i : Fin n) :
      CDerivable P (.typing Γ (.var i) (Γ.lookup i))
  | const {n : Nat} {Γ : CCtx Head n} {name : DeclName} {type : CTm Head 0} {u : Head} :
      P.constantType name = some type →
      CDerivable P (.typing .nil type (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ (.const name) type.liftClosed)
  | piForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
      {u v w : Head} :
      CDerivable P (.typing Γ A (.head u)) → R.isUniverse u →
      CDerivable P (.typing (.snoc Γ A) B (.head v)) → R.isUniverse v →
      R.join u v w → CDerivable P (.typing Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
      {u v w : Head} :
      CDerivable P (.typing Γ A (.head u)) → R.isUniverse u →
      CDerivable P (.typing (.snoc Γ A) B (.head v)) → R.isUniverse v →
      R.join u v w → CDerivable P (.typing Γ (.sigma A B) (.head w))
  /-- An abstraction has the dependent function type whose domain is its
  annotation. The annotation's formation is a premise of its own, although
  the function type's formation implies it: substituting two equal terms into
  an abstraction compares its two substituted domains, by induction on this
  premise. -/
  | lamIntro {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {body B : CTm Head (n + 1)}
      {u w : Head} :
      CDerivable P (.typing Γ A (.head w)) → R.isUniverse w →
      CDerivable P (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing (.snoc Γ A) body B) →
      CDerivable P (.typing Γ (.lam A body) (.pi A B))
  | appElim {n : Nat} {Γ : CCtx Head n} {g a A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.typing Γ g (.pi A B)) → CDerivable P (.typing Γ a A) →
      CDerivable P (.typing Γ (.app g a) (CTm.inst0 a B))
  | pairIntro {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      CDerivable P (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ a A) → CDerivable P (.typing Γ b (CTm.inst0 a B)) →
      CDerivable P (.typing Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.typing Γ p (.sigma A B)) → CDerivable P (.typing Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.typing Γ p (.sigma A B)) →
      CDerivable P (.typing Γ (.snd p) (CTm.inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {u : Head} :
      CDerivable P (.typing Γ A (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ a A) → CDerivable P (.typing Γ b A) →
      CDerivable P (.typing Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n} :
      CDerivable P (.typing Γ a A) → CDerivable P (.typing Γ (.refl a) (.id A a a))
  | sub {n : Nat} {Γ : CCtx Head n} {t A B : CTm Head n} :
      CDerivable P (.typing Γ t A) → CDerivable P (.sub Γ A B) →
      CDerivable P (.typing Γ t B)
  | conv {n : Nat} {Γ : CCtx Head n} {t A B : CTm Head n} {u : Head} :
      CDerivable P (.typing Γ t A) → CDerivable P (.equality Γ A B (.head u)) →
      R.isUniverse u → CDerivable P (.typing Γ t B)
  -- Equivalence and conversion of equality
  | refl {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n} :
      CDerivable P (.typing Γ a A) → CDerivable P (.equality Γ a a A)
  | symm {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} :
      CDerivable P (.equality Γ a b A) → CDerivable P (.equality Γ b a A)
  | trans {n : Nat} {Γ : CCtx Head n} {a b c A : CTm Head n} :
      CDerivable P (.equality Γ a b A) → CDerivable P (.equality Γ b c A) →
      CDerivable P (.equality Γ a c A)
  | convEq {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} {u : Head} :
      CDerivable P (.equality Γ a b A) → CDerivable P (.equality Γ A B (.head u)) →
      R.isUniverse u → CDerivable P (.equality Γ a b B)
  | subEq {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} :
      CDerivable P (.equality Γ a b A) → CDerivable P (.sub Γ A B) →
      CDerivable P (.equality Γ a b B)
  | headEq {n : Nat} {Γ : CCtx Head n} {h h' : Head} {A : CTm Head n} :
      R.headEq h h' → CDerivable P (.typing Γ (.head h) A) →
      CDerivable P (.typing Γ (.head h') A) →
      CDerivable P (.equality Γ (.head h) (.head h') A)
  -- Congruence
  | piCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u v w : Head} :
      CDerivable P (.equality Γ A A' (.head u)) → R.isUniverse u →
      CDerivable P (.equality (.snoc Γ A) B B' (.head v)) → R.isUniverse v →
      R.join u v w → CDerivable P (.equality Γ (.pi A B) (.pi A' B') (.head w))
  | sigmaCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u v w : Head} :
      CDerivable P (.equality Γ A A' (.head u)) → R.isUniverse u →
      CDerivable P (.equality (.snoc Γ A) B B' (.head v)) → R.isUniverse v →
      R.join u v w → CDerivable P (.equality Γ (.sigma A B) (.sigma A' B') (.head w))
  | idCong {n : Nat} {Γ : CCtx Head n} {A A' a a' b b' : CTm Head n} {u : Head} :
      CDerivable P (.equality Γ A A' (.head u)) → R.isUniverse u →
      CDerivable P (.equality Γ a a' A) → CDerivable P (.equality Γ b b' A) →
      CDerivable P (.equality Γ (.id A a b) (.id A' a' b') (.head u))
  /-- Abstractions with equal domains and equal bodies are equal. -/
  | lamCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {body body' B : CTm Head (n + 1)}
      {u w : Head} :
      CDerivable P (.equality Γ A A' (.head w)) → R.isUniverse w →
      CDerivable P (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      CDerivable P (.equality (.snoc Γ A) body body' B) →
      CDerivable P (.equality Γ (.lam A body) (.lam A' body') (.pi A B))
  | appCong {n : Nat} {Γ : CCtx Head n} {f g a b A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.equality Γ f g (.pi A B)) → CDerivable P (.equality Γ a b A) →
      CDerivable P (.equality Γ (.app f a) (.app g b) (CTm.inst0 a B))
  | pairCong {n : Nat} {Γ : CCtx Head n} {a a' b b' A : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      CDerivable P (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      CDerivable P (.equality Γ a a' A) → CDerivable P (.equality Γ b b' (CTm.inst0 a B)) →
      CDerivable P (.equality Γ (.pair a b) (.pair a' b') (.sigma A B))
  | fstCong {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.equality Γ p q (.sigma A B)) →
      CDerivable P (.equality Γ (.fst p) (.fst q) A)
  | sndCong {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.equality Γ p q (.sigma A B)) →
      CDerivable P (.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B))
  | reflCong {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} :
      CDerivable P (.equality Γ a b A) →
      CDerivable P (.equality Γ (.refl a) (.refl b) (.id A a a))
  -- Computation
  | betaPi {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n} {body B : CTm Head (n + 1)}
      {u : Head} :
      CDerivable P (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing (.snoc Γ A) body B) → CDerivable P (.typing Γ a A) →
      CDerivable P (.equality Γ (.app (.lam A body) a) (CTm.inst0 a body) (CTm.inst0 a B))
  | betaFst {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      CDerivable P (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ a A) → CDerivable P (.typing Γ b (CTm.inst0 a B)) →
      CDerivable P (.equality Γ (.fst (.pair a b)) a A)
  | betaSnd {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      CDerivable P (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ a A) → CDerivable P (.typing Γ b (CTm.inst0 a B)) →
      CDerivable P (.equality Γ (.snd (.pair a b)) b (CTm.inst0 a B))
  /-- A declared annotated root computation between two terms of one type, under
  the premises the package attaches to the step. -/
  | root {n : Nat} {Γ : CCtx Head n} {left right A : CTm Head n}
      {premises : List (CPremise Head n)} :
      P.computation.step left right → P.computation.requires left right premises →
      (∀ premise ∈ premises, CDerivable P (premise.statement Γ)) →
      CDerivable P (.typing Γ left A) → CDerivable P (.typing Γ right A) →
      CDerivable P (.equality Γ left right A)
  -- Eta
  | etaPi {n : Nat} {Γ : CCtx Head n} {f g A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.typing Γ f (.pi A B)) → CDerivable P (.typing Γ g (.pi A B)) →
      CDerivable P (.equality (.snoc Γ A)
        (.app (f.rename wk) (.var 0)) (.app (g.rename wk) (.var 0)) B) →
      CDerivable P (.equality Γ f g (.pi A B))
  | etaSigma {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      CDerivable P (.typing Γ p (.sigma A B)) → CDerivable P (.typing Γ q (.sigma A B)) →
      CDerivable P (.equality Γ (.fst p) (.fst q) A) →
      CDerivable P (.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B)) →
      CDerivable P (.equality Γ p q (.sigma A B))
  -- Cumulative subtyping
  | subEqual {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} {u : Head} :
      CDerivable P (.equality Γ A B (.head u)) → R.isUniverse u → CDerivable P (.sub Γ A B)
  | subUniv {n : Nat} {Γ : CCtx Head n} {u v : Head} :
      R.cumulative u v → CDerivable P (.sub Γ (.head u) (.head v))
  | subPi {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' w : Head} :
      CDerivable P (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ (.pi A' B') (.head u')) → R.isUniverse u' →
      CDerivable P (.equality Γ A A' (.head w)) → R.isUniverse w →
      CDerivable P (.sub (.snoc Γ A) B B') → CDerivable P (.sub Γ (.pi A B) (.pi A' B'))
  | subSigma {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' : Head} :
      CDerivable P (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      CDerivable P (.typing Γ (.sigma A' B') (.head u')) → R.isUniverse u' →
      CDerivable P (.sub Γ A A') → CDerivable P (.sub (.snoc Γ A) B B') →
      CDerivable P (.sub Γ (.sigma A B) (.sigma A' B'))
  | subTrans {n : Nat} {Γ : CCtx Head n} {A B C : CTm Head n} :
      CDerivable P (.sub Γ A B) → CDerivable P (.sub Γ B C) → CDerivable P (.sub Γ A C)

/-- `Γ ⊢ t : A`. -/
abbrev CTyped (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (t A : CTm Head n) : Prop :=
  CDerivable P (.typing Γ t A)

/-- `Γ ⊢ a ≡ b : A`. -/
abbrev CEqual (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (a b A : CTm Head n) : Prop :=
  CDerivable P (.equality Γ a b A)

/-- `Γ ⊢ A ⊑ B`. -/
abbrev CBelow (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  CDerivable P (.sub Γ A B)

theorem CDerivable.cumul {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {t : CTm Head n}
    {u v : Head} (typing : CTyped P Γ t (.head u)) (c : R.cumulative u v) :
    CTyped P Γ t (.head v) :=
  .sub typing (.subUniv c)

theorem CDerivable.cumulEq {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    {u v : Head} (equal : CEqual P Γ A B (.head u)) (c : R.cumulative u v) :
    CEqual P Γ A B (.head v) :=
  .subEq equal (.subUniv c)

/-! ## Admitted steps -/

/-- **A package admits a step in a context** when the premises it attaches to the step
are derivable there: some list of premises required of the step from `left` to `right`
has every member derivable in `Γ`. -/
def ChurchRules.Admits (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n)
    (left right : CTm Head n) : Prop :=
  ∃ premises, P.computation.requires left right premises ∧
    ∀ premise ∈ premises, CDerivable P (premise.statement Γ)

/-- **The rule for an admitted root step**: a step between two terms of one type, admitted
in their context, is an equality at the type. -/
theorem CDerivable.rootAdmitted {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}
    {left right A : CTm Head n} (step : P.computation.step left right)
    (admits : P.Admits Γ left right) (typedLeft : CTyped P Γ left A)
    (typedRight : CTyped P Γ right A) : CEqual P Γ left right A := by
  obtain ⟨_, requires, derivable⟩ := admits
  exact .root step requires derivable typedLeft typedRight

/-- **A package whose root steps require no premises.** -/
def ChurchRules.PremiseFree (P : ChurchRules R) : Prop :=
  ∀ {n : Nat} {l r : CTm Head n}, P.computation.step l r → P.computation.requires l r []

/-- A package whose steps require no premises admits each of them in every context. -/
theorem ChurchRules.PremiseFree.admits {P : ChurchRules R} (free : P.PremiseFree) {n : Nat}
    {Γ : CCtx Head n} {l r : CTm Head n} (step : P.computation.step l r) : P.Admits Γ l r :=
  ⟨[], free step, fun _ member => absurd member List.not_mem_nil⟩

/-- **The package without its premises**: the same declared constants and root steps, each
step requiring no premises. -/
def ChurchRules.withoutPremises (P : ChurchRules R) : ChurchRules R where
  constantType := P.constantType
  computation :=
    { step := P.computation.step
      rename := P.computation.rename
      substitute := P.computation.substitute }
  erase_constantType := P.erase_constantType
  erase_step := P.erase_step

theorem ChurchRules.withoutPremises_premiseFree (P : ChurchRules R) :
    P.withoutPremises.PremiseFree :=
  fun _ => rfl

/-- **The rule for a root step that requires no premises**: a step between two terms
of one type is an equality at it. -/
theorem CDerivable.rootFree {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}
    {left right A : CTm Head n} (step : P.computation.step left right)
    (typedLeft : CTyped P Γ left A) (typedRight : CTyped P Γ right A)
    (free : P.computation.requires left right [] := by exact rfl) :
    CEqual P Γ left right A :=
  .root step free (fun _ member => absurd member List.not_mem_nil) typedLeft typedRight

/-! ## Erasure of derivations -/

/-- The erasure of a statement. -/
def CStatement.erase : CStatement Head → Statement Head
  | .typing Γ t A => .typing Γ.erase t.erase A.erase
  | .equality Γ a b A => .equality Γ.erase a.erase b.erase A.erase
  | .sub Γ A B => .sub Γ.erase A.erase B.erase

theorem ChurchRules.erase_declared {P : ChurchRules R} {name : DeclName} {type : CTm Head 0}
    (declared : P.constantType name = some type) : R.constantType name = some type.erase := by
  rw [← P.erase_constantType name, declared]
  rfl

/-- **Erasure**: every annotated derivation erases to a derivation of the rule
package. -/
theorem CDerivable.erase {P : ChurchRules R} {statement : CStatement Head}
    (derivation : CDerivable P statement) : Derivable R statement.erase := by
  induction derivation with
  | headType h => exact .headType h
  | var i =>
      simp only [CStatement.erase, CTm.erase, CCtx.erase_lookup]
      exact .var i
  | const declared _ hu ih =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_liftClosed]
      exact .const (P.erase_declared declared) ih hu
  | piForm _ hu _ hv join ihA ihB => exact .piForm ihA hu ihB hv join
  | sigmaForm _ hu _ hv join ihA ihB => exact .sigmaForm ihA hu ihB hv join
  | lamIntro _ _ _ hu _ _ ihPi ihBody => exact .lamIntro ihPi hu ihBody
  | appElim _ _ ihF ihA =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS iha ihb =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihS iha ihb ⊢
      exact .pairIntro ihS hu iha ihb
  | fstElim _ ih => exact .fstElim ih
  | sndElim _ ih =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb => exact .idForm ihA hu iha ihb
  | reflIntro _ ih => exact .reflIntro ih
  | sub _ _ ihT ihLe => exact .sub ihT ihLe
  | conv _ _ hu ihT ihE => exact .conv ihT ihE hu
  | refl _ ih => exact .refl ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihE => exact .convEq ih ihE hu
  | subEq _ _ ih ihLe => exact .subEq ih ihLe
  | headEq e _ _ ih ih' => exact .headEq e ih ih'
  | piCong _ hu _ hv join ihA ihB => exact .piCong ihA hu ihB hv join
  | sigmaCong _ hu _ hv join ihA ihB => exact .sigmaCong ihA hu ihB hv join
  | idCong _ hu _ _ ihA iha ihb => exact .idCong ihA hu iha ihb
  | lamCong _ _ _ hu _ _ ihPi ihBody => exact .lamCong ihPi hu ihBody
  | appCong _ _ ihF ihA =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS iha ihb =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihS iha ihb ⊢
      exact .pairCong ihS hu iha ihb
  | fstCong _ ih => exact .fstCong ih
  | sndCong _ ih =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih => exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody iha =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihPi ihBody iha ⊢
      exact .betaPi ihPi hu ihBody iha
  | betaFst _ hu _ _ ihS iha ihb =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihS iha ihb ⊢
      exact .betaFst ihS hu iha ihb
  | betaSnd _ hu _ _ ihS iha ihb =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihS iha ihb ⊢
      exact .betaSnd ihS hu iha ihb
  | root step _ _ _ _ _ ihL ihR => exact .root (P.erase_step step) ihL ihR
  | etaPi _ _ _ ihF ihG ihBody =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_rename] at ihF ihG ihBody ⊢
      exact .etaPi ihF ihG ihBody
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [CStatement.erase, CTm.erase, CTm.erase_inst0] at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih => exact .subEqual ih hu
  | subUniv c => exact .subUniv c
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB => exact .subPi ihPi hu ihPi' hu' ihA hw ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB => exact .subSigma ihS hu ihS' hu' ihA ihB
  | subTrans _ _ ih₁ ih₂ => exact .subTrans ih₁ ih₂

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
