import Mettapedia.GSLT.Dedukti.CousineauDowekMorphism

/-!
# Conservativity of the embedding, and where exhausting stops

A map of theories is exhausting when the target has nothing between the
images that the source cannot assemble; in particular every term of the
target at the image of an interface is, up to the static equivalence, the
image of a term.  For the embedding of a pure type system the typed form of
that statement is `ExhaustsTyped`: every inhabitant of the translation of a
type is convertible to the translation of an inhabitant.

* `ExhaustsTyped` implies conservativity (`conservative_of_exhaustsTyped`):
  `Conservative` is the statement of Assaf's Theorem 5.24, that an inhabited
  translation has an inhabited source.
* `ExhaustsTyped` fails for the calculus of constructions, under confluence
  of the target (`constructions_not_exhaustsTyped`).  The witness is the one
  of Cousineau and Dowek (their Example 5): the code former of a product
  rule, not applied.  It has the translation of a type of the source
  (`bareProduct_typed`) and is convertible to the translation of no term
  (`translate_not_joinable_bareProduct`): a translation is weak eta-long,
  weak eta-long terms are closed under reduction (`WeakEtaLong.reduces`), and
  the bare code former is not weak eta-long.

So exhausting holds at most on canonical forms.  `ExhaustsCanonical` is that
statement (Proposition 14 of Cousineau and Dowek): a weak eta-long normal
inhabitant of the translation of a type is convertible to the translation of
an inhabitant.  From it, conservativity follows where translated types that
are inhabited have a weak eta-long normal inhabitant
(`conservative_of_canonical`); that is the route of their Theorem 1, which
gets such inhabitants from termination.

Not proved here: `ExhaustsCanonical` for any system, and `Conservative` for
any system.  They are named statements, used as hypotheses and conclusions of
the three implications above.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Weak eta-long terms -/

/-- **A weak eta-long term**: every occurrence of the code former of a product
rule is applied to two arguments (Definition 11 of Cousineau and Dowek). -/
inductive WeakEtaLong : Term → Prop where
  | srt (sort : Srt) : WeakEtaLong (.srt sort)
  | var (index : Nat) : WeakEtaLong (.var index)
  | con {name : String} : (∀ rule, name ≠ (Symbol.prod rule).name) → WeakEtaLong (.con name)
  | pi {domain body : Term} : WeakEtaLong domain → WeakEtaLong body → WeakEtaLong (.pi domain body)
  | lam {domain body : Term} : WeakEtaLong domain → WeakEtaLong body → WeakEtaLong (.lam domain body)
  | app {function argument : Term} :
      WeakEtaLong function → WeakEtaLong argument → WeakEtaLong (.app function argument)
  | prod (rule : ProductRule) {domain family : Term} :
      WeakEtaLong domain → WeakEtaLong family → WeakEtaLong (prodCode rule domain family)

theorem WeakEtaLong.decode (level : Srt) : WeakEtaLong (.con (Symbol.decode level).name) :=
  .con fun _ same => by
    have equal := Symbol.name_injective same
    cases equal

theorem WeakEtaLong.El {level : Srt} {term : Term} (long : WeakEtaLong term) :
    WeakEtaLong (El level term) :=
  .app (.decode level) long

/-- The bare code former is not weak eta-long. -/
theorem not_weakEtaLong_bareProduct (rule : ProductRule) :
    ¬ WeakEtaLong (.con (Symbol.prod rule).name) := by
  intro long
  generalize same : Term.con (Symbol.prod rule).name = term at long
  cases long with
  | srt sort => cases same
  | var index => cases same
  | con distinct => cases same; exact distinct rule rfl
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app _ _ => cases same
  | prod other _ _ => cases same

/-- What a weak eta-long application is made of. -/
theorem WeakEtaLong.app_inv {function argument : Term} (long : WeakEtaLong (.app function argument)) :
    (WeakEtaLong function ∧ WeakEtaLong argument) ∨
      ∃ rule domain, function = .app (.con (Symbol.prod rule).name) domain ∧
        WeakEtaLong domain ∧ WeakEtaLong argument := by
  generalize same : Term.app function argument = term at long
  cases long with
  | srt sort => cases same
  | var index => cases same
  | con _ => cases same
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app functionLong argumentLong => cases same; exact Or.inl ⟨functionLong, argumentLong⟩
  | prod rule domainLong familyLong =>
      cases same
      exact Or.inr ⟨rule, _, rfl, domainLong, familyLong⟩

/-- The parts of a weak eta-long product code are weak eta-long. -/
theorem WeakEtaLong.prodCode_inv {rule : ProductRule} {domain family : Term}
    (long : WeakEtaLong (prodCode rule domain family)) : WeakEtaLong domain ∧ WeakEtaLong family := by
  rcases long.app_inv with ⟨functionLong, familyLong⟩ | ⟨other, inner, same, domainLong, familyLong⟩
  · rcases functionLong.app_inv with ⟨headLong, _⟩ | ⟨_, _, same, _, _⟩
    · exact (not_weakEtaLong_bareProduct rule headLong).elim
    · cases same
  · obtain ⟨_, rfl⟩ := Term.app.inj same
    exact ⟨domainLong, familyLong⟩

theorem WeakEtaLong.lift {term : Term} (long : WeakEtaLong term) :
    ∀ amount cutoff : Nat, WeakEtaLong (lift amount cutoff term) := by
  induction long with
  | srt sort => intro amount cutoff; exact .srt sort
  | var index => intro amount cutoff; exact .var _
  | con distinct => intro amount cutoff; exact .con distinct
  | pi _ _ ihDomain ihBody => intro amount cutoff; exact .pi (ihDomain _ _) (ihBody _ _)
  | lam _ _ ihDomain ihBody => intro amount cutoff; exact .lam (ihDomain _ _) (ihBody _ _)
  | app _ _ ihFunction ihArgument => intro amount cutoff; exact .app (ihFunction _ _) (ihArgument _ _)
  | prod rule _ _ ihDomain ihFamily =>
      intro amount cutoff
      exact .prod rule (ihDomain _ _) (ihFamily _ _)

theorem WeakEtaLong.subst {term : Term} (long : WeakEtaLong term) :
    ∀ (target : Nat) {replacement : Term}, WeakEtaLong replacement →
      WeakEtaLong (subst target replacement term) := by
  induction long with
  | srt sort => intro target replacement _; exact .srt sort
  | var index =>
      intro target replacement replaced
      simp only [LFTyping.subst]
      split
      · exact replaced
      · split
        · exact .var _
        · exact .var _
  | con distinct => intro target replacement _; exact .con distinct
  | pi _ _ ihDomain ihBody =>
      intro target replacement replaced
      exact .pi (ihDomain _ replaced) (ihBody _ (replaced.lift 1 0))
  | lam _ _ ihDomain ihBody =>
      intro target replacement replaced
      exact .lam (ihDomain _ replaced) (ihBody _ (replaced.lift 1 0))
  | app _ _ ihFunction ihArgument =>
      intro target replacement replaced
      exact .app (ihFunction _ replaced) (ihArgument _ replaced)
  | prod rule _ _ ihDomain ihFamily =>
      intro target replacement replaced
      exact .prod rule (ihDomain _ replaced) (ihFamily _ replaced)

/-- A translation is weak eta-long. -/
theorem translate_weakEtaLong (term : PTerm) : WeakEtaLong (translate term) := by
  induction term with
  | var index => exact .var index
  | sort level =>
      exact .con fun _ same => by
        have equal := Symbol.name_injective same
        cases equal
  | pi rule domain body ihDomain ihBody => exact .prod rule ihDomain (.lam ihDomain.El ihBody)
  | lam level domain body ihDomain ihBody => exact .lam ihDomain.El ihBody
  | app function argument ihFunction ihArgument => exact .app ihFunction ihArgument

variable {profile : Profile}

/-- A root contraction of the embedding keeps a term weak eta-long. -/
theorem WeakEtaLong.rootStep {source target : Term} (long : WeakEtaLong source)
    (step : RootStep (cdTheory profile) source target) : WeakEtaLong target := by
  cases step with
  | beta domain body argument =>
      rcases long.app_inv with ⟨functionLong, argumentLong⟩ | ⟨_, _, same, _, _⟩
      · generalize shape : Term.lam domain body = function at functionLong
        cases functionLong with
        | lam _ bodyLong => cases shape; exact bodyLong.subst 0 argumentLong
        | srt sort => cases shape
        | var index => cases shape
        | con _ => cases shape
        | pi _ _ => cases shape
        | app _ _ => cases shape
        | prod rule _ _ => cases shape
      · cases same
  | delta defined => cases defined
  | @rule declared assignment member =>
      cases member with
      | @code source target _ =>
          exact .con fun _ same => by
            have equal := Symbol.name_injective same
            cases equal
      | @prod rule _ =>
          rw [inst_prodRule_lhs] at long
          rw [inst_prodRule_rhs]
          rcases long.app_inv with ⟨_, codeLong⟩ | ⟨_, _, same, _, _⟩
          · obtain ⟨domainLong, familyLong⟩ := codeLong.prodCode_inv
            exact .pi domainLong.El (WeakEtaLong.El (.app (familyLong.lift 1 0) (.var 0)))
          · cases same

/-- **Weak eta-long terms are closed under the steps of the embedding.** -/
theorem WeakEtaLong.step {source : Term} (long : WeakEtaLong source) :
    ∀ {target : Term}, Step (cdTheory profile) source target → WeakEtaLong target := by
  induction long with
  | srt sort => intro target step; exact (srt_normal (cdTheory_headed profile) sort _ step).elim
  | var index => intro target step; exact (var_normal (cdTheory_headed profile) index _ step).elim
  | @con name distinct =>
      intro target step
      exact (WeakEtaLong.con distinct).rootStep step.con_inv
  | pi domainLong bodyLong ihDomain ihBody =>
      intro target step
      rcases step.pi_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact (RootStep.not_pi (cdTheory_headed profile) root).elim
      · exact .pi (ihDomain inner) bodyLong
      · exact .pi domainLong (ihBody inner)
  | lam domainLong bodyLong ihDomain ihBody =>
      intro target step
      rcases step.lam_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact (RootStep.not_lam (cdTheory_headed profile) root).elim
      · exact .lam (ihDomain inner) bodyLong
      · exact .lam domainLong (ihBody inner)
  | app functionLong argumentLong ihFunction ihArgument =>
      intro target step
      rcases step.app_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact (WeakEtaLong.app functionLong argumentLong).rootStep root
      · exact .app (ihFunction inner) argumentLong
      · exact .app functionLong (ihArgument inner)
  | prod rule domainLong familyLong ihDomain ihFamily =>
      intro target step
      rcases step.app_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact (RootStep.not_of_rigid (cdTheory_headed profile)
          (cdTheory_not_defines_prod profile rule) rfl root).elim
      · rcases inner.app_inv with root | ⟨_, deeper, rfl⟩ | ⟨_, deeper, rfl⟩
        · exact (RootStep.not_of_rigid (cdTheory_headed profile)
            (cdTheory_not_defines_prod profile rule) rfl root).elim
        · exact (RootStep.not_of_rigid (cdTheory_headed profile)
            (cdTheory_not_defines_prod profile rule) rfl deeper.con_inv).elim
        · exact .prod rule (ihDomain deeper) familyLong
      · exact .prod rule domainLong (ihFamily inner)

theorem WeakEtaLong.reduces {source target : Term} (long : WeakEtaLong source)
    (reduces : Reduces (cdTheory profile) source target) : WeakEtaLong target := by
  induction reduces with
  | refl => exact long
  | tail _ step ih => exact ih.step step

/-- The bare code former has no step. -/
theorem bareProduct_normal (profile : Profile) (rule : ProductRule) :
    IsNormal (Step (cdTheory profile)) (.con (Symbol.prod rule).name) :=
  fun _ step => RootStep.not_of_rigid (cdTheory_headed profile)
    (cdTheory_not_defines_prod profile rule) rfl step.con_inv

/-- **No translation has a common reduct with the bare code former.** -/
theorem translate_not_joinable_bareProduct (profile : Profile) (rule : ProductRule) (term : PTerm) :
    ¬ Joinable (cdTheory profile) (translate term) (.con (Symbol.prod rule).name) := by
  rintro ⟨common, leftReduces, rightReduces⟩
  have same := (bareProduct_normal profile rule).reflTransGen_eq rightReduces
  rw [same] at leftReduces
  exact not_weakEtaLong_bareProduct rule ((translate_weakEtaLong term).reduces leftReduces)

/-! ## The typed statements -/

/-- **Exhausting, on typed terms**: every inhabitant of the translation of a
type is convertible to the translation of an inhabitant. -/
def ExhaustsTyped (profile : Profile) : Prop :=
  ∀ (context : SortedCtx) (type : PTerm) (level : Srt) (inhabitant : Term),
    Derives profile context (.type type level) →
    LambdaPiModulo (cdTheory profile) (translateCtx context) inhabitant (El level (translate type)) →
      ∃ source, Derives profile context (.term source type level) ∧
        Conv (cdTheory profile) (translate source) inhabitant

/-- **Exhausting on canonical forms**: the same for inhabitants that are
normal and weak eta-long. -/
def ExhaustsCanonical (profile : Profile) : Prop :=
  ∀ (context : SortedCtx) (type : PTerm) (level : Srt) (inhabitant : Term),
    Derives profile context (.type type level) →
    IsNormal (Step (cdTheory profile)) inhabitant → WeakEtaLong inhabitant →
    LambdaPiModulo (cdTheory profile) (translateCtx context) inhabitant (El level (translate type)) →
      ∃ source, Derives profile context (.term source type level) ∧
        Conv (cdTheory profile) (translate source) inhabitant

/-- **Conservativity**: a type whose translation is inhabited is inhabited. -/
def Conservative (profile : Profile) : Prop :=
  ∀ (context : SortedCtx) (type : PTerm) (level : Srt) (inhabitant : Term),
    Derives profile context (.type type level) →
    LambdaPiModulo (cdTheory profile) (translateCtx context) inhabitant (El level (translate type)) →
      ∃ source, Derives profile context (.term source type level)

/-- Inhabited translations of types have a weak eta-long normal inhabitant. -/
def CanonicalInhabitants (profile : Profile) : Prop :=
  ∀ (context : SortedCtx) (type : PTerm) (level : Srt) (inhabitant : Term),
    Derives profile context (.type type level) →
    LambdaPiModulo (cdTheory profile) (translateCtx context) inhabitant (El level (translate type)) →
      ∃ canonical, IsNormal (Step (cdTheory profile)) canonical ∧ WeakEtaLong canonical ∧
        LambdaPiModulo (cdTheory profile) (translateCtx context) canonical (El level (translate type))

/-- Exhausting on typed terms gives conservativity. -/
theorem conservative_of_exhaustsTyped (exhausts : ExhaustsTyped profile) : Conservative profile :=
  fun context type level inhabitant formed typed =>
    (exhausts context type level inhabitant formed typed).imp fun _ found => found.1

/-- Exhausting on typed terms gives exhausting on canonical forms. -/
theorem exhaustsCanonical_of_exhaustsTyped (exhausts : ExhaustsTyped profile) :
    ExhaustsCanonical profile :=
  fun context type level inhabitant formed _ _ typed =>
    exhausts context type level inhabitant formed typed

/-- **Exhausting on canonical forms gives conservativity**, where inhabited
translations have canonical inhabitants. -/
theorem conservative_of_canonical (exhausts : ExhaustsCanonical profile)
    (canonical : CanonicalInhabitants profile) : Conservative profile := by
  intro context type level inhabitant formed typed
  obtain ⟨normal, isNormal, long, normalTyped⟩ := canonical context type level inhabitant formed typed
  exact (exhausts context type level normal formed isNormal long normalTyped).imp
    fun _ found => found.1

/-! ## Exhausting fails beyond canonical forms -/

namespace Example

/-- The type `Π X : Type. (X → Type) → Type` of the calculus of
constructions. -/
def productFormerType : PTerm :=
  .pi LFProfile.kindKindKind (.sort .type)
    (.pi LFProfile.kindKindKind (.pi LFProfile.typeKindKind (.var 0) (.sort .type)) (.sort .type))

theorem productFormerType_formed :
    Derives constructions [] (.type productFormerType .kind) := by
  have family : Derives constructions [(.sort .type, .kind)]
      (.type (.pi LFProfile.typeKindKind (.var 0) (.sort .type)) .kind) :=
    .pi variable_is_type (.sort rfl) (by decide)
  exact .pi (.sort rfl) (.pi family (.sort rfl) (by decide)) (by decide)

/-- The translation of that type is convertible to the declared type of the
code former of `(Type, Type, Type)`. -/
theorem productFormerType_conv :
    Conv (cdTheory constructions)
      (.pi (codeType .type) (.pi (.pi (El .type (.var 0)) (codeType .type)) (codeType .type)))
      (El .kind (translate productFormerType)) := by
  have kind : Conv (cdTheory constructions) (El .kind (sortCode .type)) (codeType .type) :=
    conv_code (profile := constructions) rfl
  have inner : Conv (cdTheory constructions)
      (El .kind (translate (.pi LFProfile.typeKindKind (.var 0) (.sort .type))))
      (.pi (El .type (.var 0)) (codeType .type)) :=
    .trans _ _ _ (conv_prod (profile := constructions) (rule := LFProfile.typeKindKind)
      (by decide) _ _ _) (Conv.pi (.refl _) kind)
  have middle : Conv (cdTheory constructions)
      (El .kind (translate (.pi LFProfile.kindKindKind
        (.pi LFProfile.typeKindKind (.var 0) (.sort .type)) (.sort .type))))
      (.pi (.pi (El .type (.var 0)) (codeType .type)) (codeType .type)) :=
    .trans _ _ _ (conv_prod (profile := constructions) (rule := LFProfile.kindKindKind)
      (by decide) _ _ _) (Conv.pi inner kind)
  have outer : Conv (cdTheory constructions) (El .kind (translate productFormerType))
      (.pi (codeType .type) (.pi (.pi (El .type (.var 0)) (codeType .type)) (codeType .type))) :=
    .trans _ _ _ (conv_prod (profile := constructions) (rule := LFProfile.kindKindKind)
      (by decide) _ _ _) (Conv.pi kind middle)
  exact .symm _ _ outer

/-- **The bare code former has the translation of a type of the source.** -/
theorem bareProduct_typed :
    LambdaPiModulo (cdTheory constructions) []
      (.con (Symbol.prod LFProfile.typeTypeType).name) (El .kind (translate productFormerType)) := by
  have declared : LambdaPiModulo (cdTheory constructions) []
      (.con (Symbol.prod LFProfile.typeTypeType).name)
      (.pi (codeType .type) (.pi (.pi (El .type (.var 0)) (codeType .type)) (codeType .type))) :=
    .con (by rw [constType_symbol]; decide)
  exact .conv declared productFormerType_conv (type_El (translate_sound productFormerType_formed))

end Example

/-- **Where confluence is used**: the embedding of the calculus of
constructions is not exhausting on typed terms. -/
theorem constructions_not_exhaustsTyped (confluent : Confluent (Step (cdTheory constructions))) :
    ¬ ExhaustsTyped constructions := by
  intro exhausts
  obtain ⟨source, _, convertible⟩ := exhausts [] Example.productFormerType .kind _
    Example.productFormerType_formed Example.bareProduct_typed
  exact translate_not_joinable_bareProduct constructions LFProfile.typeTypeType source
    ((conv_iff_joinable confluent).mp convertible)

#print axioms WeakEtaLong.step
#print axioms translate_not_joinable_bareProduct
#print axioms conservative_of_canonical
#print axioms Example.bareProduct_typed
#print axioms constructions_not_exhaustsTyped

end Mettapedia.GSLT.Dedukti
