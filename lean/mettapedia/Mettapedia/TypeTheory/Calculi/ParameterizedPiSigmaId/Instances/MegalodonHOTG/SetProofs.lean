import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetLaws
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# The proofs of the logic of the sets are terms of the package

`MegalodonHOTG.SetLaws` translates the types and the terms of the higher-order logic of the sets into
terms of the tower inside the sets with the constants of set theory (`tyTm`, `trTerm`), and
declares the eleven laws of the sets as proof constants (`setLaws`). This file translates the
proofs: **every proof of the checker's calculus of the logic is a term of the package, of the
type of the proofs of the term of its conclusion**, in every presentation of the proofs whose
laws hold in the package. A statement derived from the laws is then a closed term that the
judgment types. The same holds in the set theory on rule constants (`setTheoryRules`), where
the proofs are built from rule constants and nothing unfolds.

**The calculus** (`ProofSyntaxModulo`): hypotheses, the introduction and elimination rules of
implication and of the universal quantifier, and retyping along conversion, which is generated
by β and by instances of listed defining equations.

**The translation commutes with renaming and with substitution** (`trWith_rename`,
`trWith_subst`, `trWith_instantiate`): the term of a renamed term is the renamed term, along
the renaming of indices that the renaming of variables induces (`indexRen`), and the term of
an instance is the term of the body with the term of the argument for its newest variable.

**Conversion is typed equality** (`trWith_conversion`): in every package over the set theory,
terms of the logic related by β, and by instances of defining equations that hold in the
package, have equal terms, at the term of their type and in the context of their variables.
By β alone no equation is asked for (`trWith_betaConversion`). So the proofs of convertible
statements are equal types (`holds_conversion`, `holds_betaConversion`). A defining equation
holds in a package when the terms of its two sides are equal there (`EquationsHold`).

**A presentation of the proofs** (`ProofOps`): four terms that introduce and eliminate
implication and the universal quantifier. Its laws in a package (`ProofOps.Lawful`): each of
the four has the type of the proofs of the conclusion of its rule whenever its arguments are
typed as the premises of the rule. Two presentations:

* **by the equations** (`equationOps`): the introduction of an implication is an abstraction
  over the proofs of the premise, and its elimination an application; the introduction of a
  universal statement is an abstraction over the term of the type, and its elimination an
  application to the term of the instance. Its laws hold in every package over the set theory
  that contains the steps of its equations (`equationOps_lawful`): the proofs of an implication
  are the functions between the proofs (`holds_imp_rule`, from the equation `holdsImp`), and
  the proofs of a quantification of an abstraction are the dependent functions into the
  proofs of its body (`holds_all_lam_rule`, from the equation `holdsAll` and β);
* **by the rule constants** (`ruleOps`): `impI p q (λ (h : holds p). b)`, `impE p q f a`,
  `allI T (λ T φ) (λ (x : T). b)` and `allE T (λ T φ) h t`. Its laws hold in every package
  that declares the rule constants (`OverSetTheoryRules`, `ruleOps_lawful`); the instance is
  the β-step between `(λ T φ) t` and `φ` at `t`. The typings of the rule constants are stated
  here (`impI_typed`, `impE_typed`, `allI_typed`, `allE_typed`, `eqI_typed`, `eqE_typed`,
  `elemTheLaw_typed`, `theElemLaw_typed`, and the applied forms `cImpI_typed`,
  `cImpE_typed`, `cAllI_typed`, `cAllE_typed`).

**Every proof is a term** (`trProof`, `trProof_typed`), in every package over the set theory
and for every presentation whose laws hold there. Given a context of the package, a placement
of the variables of the logic at variables of the context whose types are the terms of their
types, and for each hypothesis a term of the type of the proofs of its placed term:

* a hypothesis is its term; with the hypotheses placed at variables it is a variable
  (`trProof_typed_at`), and the context of a sequent, its variables followed by its
  hypotheses, is such a context (`trProof_sequent_typed`);
* each rule of implication and of the universal quantifier is the term of the presentation
  for it, and its typing is the law of the presentation for it;
* a retyping leaves the term as it is: the two types of proofs are equal.

**From the laws** (`lawProof_typed`, `expandedLawProof_typed`, `lawProof_exists`): a closed
proof from the eleven laws, as written or with their connectives written out, is a closed
term of the package with the laws, each hypothesis discharged by the proof constant of its
law, in the presentation by the equations. What is proved this way is true in the model of
the logic (`lawProof_sound`), relative to cofinally many inaccessible cardinals in two
universes.

**On the rule constants** (`ruleLaws`): the eleven laws as proof constants over the set theory
on rule constants, and no equation (`ruleLaws_typed`). It has a set model and is consistent
(`ruleLaws_setModel`, `ruleLaws_consistent`), and every term typed in a formed context of it is
strongly normalizing (`ruleLaws_sn`); a closed proof from the laws is a closed term of
it through the presentation by the rule constants (`ruleLawProof_typed`,
`ruleLawProof_exists`), and what is proved this way is true in the model of the logic
(`ruleLawProof_sound`). Falsity has no closed proof in the set theory on rule constants
(`setTheoryRules_no_proof_falsity`).

**The connectives.** The full natural deduction has rules for truth, falsity, negation,
conjunction, disjunction and the existential quantifier. Its proofs by these rules elaborate
to proofs of the calculus above in which the connectives are written out by implication and
quantification (`expandProofModulo?`). A term of the logic and the same term with its
connectives written out have equal terms in the package (`trWith_expandInline`): the same
term when there is no existential quantifier (`trWith_expandInline_eq`), and otherwise terms
that differ by the application of a predicate to its bound variable (`trTerm_ex_ne`). So a
proof of the full calculus by the rules of the hypotheses, the connectives and the quantifiers
is a term for its statement (`trFullProof?`, `trFullProof?_typed`), and from the eleven laws a
closed term of the package with the laws (`fullLawProof_typed`, `fullLawProof_exists`).

**Not covered**: the equality rules of the full calculus: reflexivity, symmetry and
transitivity, congruence under application and abstraction, extensionality of functions and
of propositions, and β and η as equalities. The calculus modulo conversion has no rule for
them, and its conversion is not extended here to stand for them.

The package with the laws on rule constants is strongly normalizing (`ruleLaws_sn`). Nothing
here says that the packages with the equations normalize, or that a procedure decides these
typings: the terms are typed in the declarative judgment, by conversion along the equations
or by the types of the rule constants.

Positive examples: from the law of the empty set, **the empty set is a subset of every set**,
`∀ x. ∀ y. y ∈ Empty → y ∈ x` (`emptySubsetProof`). The term of the proof by the equations is
`λ x y. λ h : holds (In y Empty). emptyLaw y h (In y x)` (`emptySubsetTerm`,
`trProof_emptySubsetProof`), a closed term of the package with the laws, of the type of the
proofs of the statement (`emptySubset_typed`). The proof of the same statement in the full
calculus, from the law as written with its negation, has the same term
(`trFullProof?_emptySubsetFullProof`). A retyping leaves the term as it is
(`trProof_powerRetyping`). A defining equation whose sides are convertible by β holds in every
package over the set theory (`memberEmptyAt_holds`).

Positive examples on the rule constants: the term of the same proof by the rule constants
(`emptySubsetRuleTerm`, `trProof_ruleOps_emptySubsetProof`) is a closed term of the package
with the laws on rule constants (`emptySubsetRule_typed`). From the law of the empty set, by
the four rules, a closed proof that no set is a member of the empty set (`noMemberProof`,
`noMemberTerm`, `noMemberTerm_typed`), used by `allE` at `Power Empty` and at the universe at a
level read as a set (`noMemberAt_powerEmpty`, `noMemberAt_universe`); as a function on the
sets applied to a set it takes a β-step, and the reduct keeps its type by the theorem on
declared constants with no equation (`noMemberApplied_step`,
`noMemberApplied_powerEmpty_step`, `noMemberApplied_universe_step`); at `Power Empty` it is
strongly normalizing (`noMemberApplied_powerEmpty_sn`). Where both presentations
apply, in a package with the equations and the rule constants (`lawsWithRules`), the terms of
a proof by the two have the same type (`presentations_agree`,
`emptySubset_presentations_agree`).

Negative examples: no closed term of the package with the laws proves that the empty set is a
member of itself, so **no proof of the logic from the eleven laws concludes it**
(`no_proof_emptyInEmpty`, `no_fullProof_emptyInEmpty`), relative to cofinally many
inaccessible cardinals in two universes. The defining equation that makes that statement the
true statement does not hold in the package with the laws (`emptyInEmptyTrue_not_hold`). The
two presentations give different terms for one proof (`emptySubsetTerm_ne_ruleTerm`).

**The power set of a set lies in its universe.** For every set `N`, `Power N ∈ UnivOf N`
(`powerInUniverseFormula`). The proof from `N ∈ UnivOf N` and the closure of `UnivOf N`, with
the conjunction written out (`powerInUniverseProof`), is a closed term by the equations
(`powerInUniverseTerm`, `powerInUniverseTerm_typed`) and a closed term by the rule constants
(`powerInUniverseRuleTerm`, `powerInUniverseRule_typed`); the two terms differ
(`powerInUniverseTerm_ne_ruleTerm`). At `Empty` and at the universe at a level it proves the
instance (`powerInUniverseAt_empty`, `powerInUniverseAt_universe`). The statement is true in
the model of the logic, and that truth is the membership `powerInUniverse_true` records
(`powerInUniverse_sound`, `powerInUniverse_agrees`). The term by the rule constants is strongly
normalizing (`powerInUniverseRule_sn`). The type of the proofs of the statement takes no step
in the set theory on rule constants (`powerInUniverse_noStep`); in the set theory with
equations it unfolds by one declared step (`powerInUniverse_unfolds`). Negative example: the
converse `∀ N. UnivOf N ∈ Power N` is false in the model, so no closed term of the package
with the laws on rule constants has the type of its proofs (`universeInPower_false`,
`universeInPower_no_term`).

A pair of a set and a proof that a predicate holds of it keeps the set: `fst` of the pair
is the set (`witnessFst_typed`, `witnessFst_equal`, `witnessFst_value`), and the pair type
is a type of `allClasses` (`witnessPairType_typed`). The existential quantifier written with
`imp` and `all` is introduced by `λ R k. k a p` where the equations make the proofs functions
(`setTheory_exIntro_typed`), and by the rule constants where nothing unfolds
(`setTheoryRules_exIntro_typed`); either proof eliminates into any proposition
(`setTheory_exElim_typed`, `setTheoryRules_exElim_typed`). In the set model of either package
the two introductions denote the one member of a truth value (`exHolds_truthCode`), so no
closed function of the proof returns both witnesses when their values differ
(`no_existence_witness`, `setTheory_emptyOr_no_witness`, `setTheoryRules_emptyOr_no_witness`).
The predicate `λ x. x = Empty ∨ x = Power Empty` has both witnesses. `λ h. Eps P` is a
function of that type (`epsAsWitness_typed`) and returns `epsChoice` (`epsAsWitness_value`),
so it fails at one of the two (`setTheory_epsAsWitness_misses`,
`setTheoryRules_epsAsWitness_misses`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL (Ty Ctx Var Term Formula ClosedFormula Rename Subst weakenHyps
  SourceStep CoreConversion ProofSyntaxModulo ProofSyntax)
open Mettapedia.Logic (HOL.rename HOL.subst HOL.instantiate HOL.weaken HOL.DefiningEquation)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (expandInline existentialInline
  conjunctionFormula disjunctionFormula truth falsity connectiveFragment expandProofModulo?
  expandProofModulo?_isSome)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetHenkinInterpretation (emptyLaw)
open ZFSetUniverseInterpretation (UniverseSymbol embed universeTheory universeModel inSet
  subsetFormula)

universe u

variable {L : Type}

/-! ## The translation commutes with renaming and with substitution -/

section Commutation

variable {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)

/-- **The renaming of indices that a renaming of variables induces**: the index of a variable
goes to the index of its image. -/
def indexRen : {Γ Δ : Ctx Unit} → Rename Unit Γ Δ → Ren Γ.length Δ.length
  | [], _, _ => Fin.elim0
  | _ :: _, _, ρ => Fin.cases (varIndex (ρ .vz)) (indexRen fun {_} v => ρ (.vs v))

/-- The induced renaming sends the index of a variable to the index of its image. -/
theorem indexRen_varIndex : ∀ {Γ Δ : Ctx Unit} (ρ : Rename Unit Γ Δ) {A : Ty Unit} (v : Var Γ A),
    indexRen ρ (varIndex v) = varIndex (ρ v)
  | _ :: _, _, _, _, .vz => rfl
  | _ :: _, _, ρ, _, .vs v => indexRen_varIndex (fun {_} w => ρ (.vs w)) v

/-- Every index is the index of a variable. -/
theorem varIndex_surjective : ∀ {Γ : Ctx Unit} (i : Fin Γ.length),
    ∃ (A : Ty Unit) (v : Var Γ A), varIndex v = i
  | [], i => i.elim0
  | _ :: _, i => by
    refine Fin.cases ⟨_, .vz, rfl⟩ (fun j => ?_) i
    obtain ⟨A, v, rfl⟩ := varIndex_surjective j
    exact ⟨A, .vs v, rfl⟩

/-- Lifting a renaming of indices follows lifting the renaming of variables. -/
theorem liftRen_agrees {Γ Δ : Ctx Unit} {ρ : Rename Unit Γ Δ} {r : Ren Γ.length Δ.length}
    (agrees : ∀ {A : Ty Unit} (v : Var Γ A), r (varIndex v) = varIndex (ρ v)) {σ : Ty Unit} :
    ∀ {A : Ty Unit} (v : Var (σ :: Γ) A),
      liftRen r (varIndex v) = varIndex (Rename.lift (σ := σ) ρ v)
  | _, .vz => rfl
  | _, .vs v => congrArg Fin.succ (agrees v)

/-- **The translation commutes with renaming**, for every renaming of indices that sends the
index of a variable to the index of its image. -/
theorem trWith_rename_of {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    ∀ {Δ : Ctx Unit} {ρ : Rename Unit Γ Δ} {r : Ren Γ.length Δ.length},
      (∀ {B : Ty Unit} (v : Var Γ B), r (varIndex v) = varIndex (ρ v)) →
        (trWith name (HOL.rename ρ t) : CTm (Head L) Δ.length) = (trWith name t).rename r := by
  induction t with
  | var v => exact fun agrees => congrArg CTm.var (agrees v).symm
  | const c => exact fun _ => rfl
  | app f x ihf ihx => exact fun agrees => congrArg₂ CTm.app (ihf agrees) (ihx agrees)
  | @lam σ Γ τ body ih =>
    intro Δ ρ r agrees
    show CTm.lam (tyTm σ) (trWith name (HOL.rename (Rename.lift ρ) body)) =
      CTm.lam ((tyTm σ).rename r) ((trWith name body).rename (liftRen r))
    rw [tyTm_rename, ih (liftRen_agrees agrees)]
  | top => exact fun _ => rfl
  | bot => exact fun _ => rfl
  | and p q ihp ihq =>
    intro Δ ρ r agrees
    show cAnd (trWith name (HOL.rename ρ p)) (trWith name (HOL.rename ρ q)) = _
    rw [ihp agrees, ihq agrees]
    exact (cAnd_rename r _ _).symm
  | or p q ihp ihq =>
    intro Δ ρ r agrees
    show cOr (trWith name (HOL.rename ρ p)) (trWith name (HOL.rename ρ q)) = _
    rw [ihp agrees, ihq agrees]
    exact (cOr_rename r _ _).symm
  | imp p q ihp ihq =>
    exact fun agrees => congrArg₂ (fun a b => cImp a b) (ihp agrees) (ihq agrees)
  | not p ih =>
    intro Δ ρ r agrees
    show cNot (trWith name (HOL.rename ρ p)) = _
    rw [ih agrees]
    rfl
  | @eq Γ τ x y ihx ihy =>
    intro Δ ρ r agrees
    show cEq (tyTm τ) (trWith name (HOL.rename ρ x)) (trWith name (HOL.rename ρ y)) =
      cEq ((tyTm τ).rename r) ((trWith name x).rename r) ((trWith name y).rename r)
    rw [tyTm_rename, ihx agrees, ihy agrees]
  | @all σ Γ p ih =>
    intro Δ ρ r agrees
    show cAll (tyTm σ) (.lam (tyTm σ) (trWith name (HOL.rename (Rename.lift ρ) p))) =
      cAll ((tyTm σ).rename r) (.lam ((tyTm σ).rename r) ((trWith name p).rename (liftRen r)))
    rw [tyTm_rename, ih (liftRen_agrees agrees)]
  | @ex σ Γ p ih =>
    intro Δ ρ r agrees
    show cEx (tyTm σ) (.lam (tyTm σ) (trWith name (HOL.rename (Rename.lift ρ) p))) = _
    rw [ih (liftRen_agrees agrees)]
    show _ = (cEx (tyTm σ) (.lam (tyTm σ) (trWith name p))).rename r
    rw [cEx_rename]
    show _ = cEx ((tyTm σ).rename r)
      (.lam ((tyTm σ).rename r) ((trWith name p).rename (liftRen r)))
    rw [tyTm_rename]

/-- **The translation commutes with renaming.** -/
theorem trWith_rename {Γ Δ : Ctx Unit} {A : Ty Unit} (ρ : Rename Unit Γ Δ) (t : Term Const Γ A) :
    (trWith name (HOL.rename ρ t) : CTm (Head L) Δ.length) =
      (trWith name t).rename (indexRen ρ) :=
  trWith_rename_of name t (indexRen_varIndex ρ)

/-- The translation of a weakened term is the weakened translation. -/
theorem trWith_weaken {Γ : Ctx Unit} {A σ : Ty Unit} (t : Term Const Γ A) :
    (trWith name (HOL.weaken (σ := σ) t) : CTm (Head L) (Γ.length + 1)) =
      (trWith name t).rename wk :=
  trWith_rename_of name t fun _ => rfl

/-- **The substitution of indices that a substitution of variables induces**: the index of a
variable goes to the term of its image. -/
def indexSub : {Γ Δ : Ctx Unit} → Subst Const Γ Δ → CSub (Head L) Γ.length Δ.length
  | [], _, _ => Fin.elim0
  | _ :: _, _, s => Fin.cases (trWith name (s .vz)) (indexSub fun {_} v => s (.vs v))

/-- The induced substitution sends the index of a variable to the term of its image. -/
theorem indexSub_varIndex : ∀ {Γ Δ : Ctx Unit} (s : Subst Const Γ Δ) {A : Ty Unit} (v : Var Γ A),
    (indexSub name s (varIndex v) : CTm (Head L) Δ.length) = trWith name (s v)
  | _ :: _, _, _, _, .vz => rfl
  | _ :: _, _, s, _, .vs v => indexSub_varIndex (fun {_} w => s (.vs w)) v

/-- Lifting a substitution of indices follows lifting the substitution of variables. -/
theorem liftSub_agrees {Γ Δ : Ctx Unit} {s : Subst Const Γ Δ}
    {c : CSub (Head L) Γ.length Δ.length}
    (agrees : ∀ {A : Ty Unit} (v : Var Γ A), c (varIndex v) = trWith name (s v)) {σ : Ty Unit} :
    ∀ {A : Ty Unit} (v : Var (σ :: Γ) A),
      CTm.liftSub c (varIndex v) = trWith name (Subst.lift (σ := σ) s v)
  | _, .vz => rfl
  | _, .vs v => by
    show (c (varIndex v)).rename wk = trWith name (HOL.weaken (s v))
    rw [agrees v, trWith_weaken]

/-- **The translation commutes with substitution**, for every substitution of indices that
sends the index of a variable to the term of its image. -/
theorem trWith_subst_of {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    ∀ {Δ : Ctx Unit} {s : Subst Const Γ Δ} {c : CSub (Head L) Γ.length Δ.length},
      (∀ {B : Ty Unit} (v : Var Γ B), c (varIndex v) = trWith name (s v)) →
        trWith name (HOL.subst s t) = (trWith name t).subst c := by
  induction t with
  | var v => exact fun agrees => (agrees v).symm
  | const c => exact fun _ => rfl
  | app f x ihf ihx => exact fun agrees => congrArg₂ CTm.app (ihf agrees) (ihx agrees)
  | @lam σ Γ τ body ih =>
    intro Δ s c agrees
    show CTm.lam (tyTm σ) (trWith name (HOL.subst (Subst.lift s) body)) =
      CTm.lam ((tyTm σ).subst c) ((trWith name body).subst (CTm.liftSub c))
    rw [tyTm_subst, ih (liftSub_agrees name agrees)]
  | top => exact fun _ => rfl
  | bot => exact fun _ => rfl
  | and p q ihp ihq =>
    intro Δ s c agrees
    show cAnd (trWith name (HOL.subst s p)) (trWith name (HOL.subst s q)) = _
    rw [ihp agrees, ihq agrees]
    exact (cAnd_subst c _ _).symm
  | or p q ihp ihq =>
    intro Δ s c agrees
    show cOr (trWith name (HOL.subst s p)) (trWith name (HOL.subst s q)) = _
    rw [ihp agrees, ihq agrees]
    exact (cOr_subst c _ _).symm
  | imp p q ihp ihq =>
    exact fun agrees => congrArg₂ (fun a b => cImp a b) (ihp agrees) (ihq agrees)
  | not p ih =>
    intro Δ s c agrees
    show cNot (trWith name (HOL.subst s p)) = _
    rw [ih agrees]
    rfl
  | @eq Γ τ x y ihx ihy =>
    intro Δ s c agrees
    show cEq (tyTm τ) (trWith name (HOL.subst s x)) (trWith name (HOL.subst s y)) =
      cEq ((tyTm τ).subst c) ((trWith name x).subst c) ((trWith name y).subst c)
    rw [tyTm_subst, ihx agrees, ihy agrees]
  | @all σ Γ p ih =>
    intro Δ s c agrees
    show cAll (tyTm σ) (.lam (tyTm σ) (trWith name (HOL.subst (Subst.lift s) p))) =
      cAll ((tyTm σ).subst c) (.lam ((tyTm σ).subst c) ((trWith name p).subst (CTm.liftSub c)))
    rw [tyTm_subst, ih (liftSub_agrees name agrees)]
  | @ex σ Γ p ih =>
    intro Δ s c agrees
    show cEx (tyTm σ) (.lam (tyTm σ) (trWith name (HOL.subst (Subst.lift s) p))) = _
    rw [ih (liftSub_agrees name agrees)]
    show _ = (cEx (tyTm σ) (.lam (tyTm σ) (trWith name p))).subst c
    rw [cEx_subst]
    show _ = cEx ((tyTm σ).subst c)
      (.lam ((tyTm σ).subst c) ((trWith name p).subst (CTm.liftSub c)))
    rw [tyTm_subst]

/-- **The translation commutes with substitution.** -/
theorem trWith_subst {Γ Δ : Ctx Unit} {A : Ty Unit} (s : Subst Const Γ Δ) (t : Term Const Γ A) :
    (trWith name (HOL.subst s t) : CTm (Head L) Δ.length) =
      (trWith name t).subst (indexSub name s) :=
  trWith_subst_of name t (indexSub_varIndex name s)

/-- **The translation commutes with instantiation**: the term of an instance is the term of
the body with the term of the argument for its newest variable. -/
theorem trWith_instantiate {Γ : Ctx Unit} {σ A : Ty Unit} (t : Term Const Γ σ)
    (body : Term Const (σ :: Γ) A) :
    (trWith name (HOL.instantiate t body) : CTm (Head L) Γ.length) =
      CTm.inst0 (trWith name t) (trWith name body) :=
  trWith_subst_of name body fun {_} v => by
    cases v with
    | vz => rfl
    | vs v => rfl

/-- The term of a renamed term of the logic of the sets is the renamed term. -/
theorem trTerm_rename {Γ Δ : Ctx Unit} {A : Ty Unit} (ρ : Rename Unit Γ Δ)
    (t : Term UniverseSymbol Γ A) :
    (trTerm (HOL.rename ρ t) : CTm (Head L) Δ.length) = (trTerm t).rename (indexRen ρ) :=
  trWith_rename constName ρ t

/-- The term of a substituted term of the logic of the sets is the substituted term. -/
theorem trTerm_subst {Γ Δ : Ctx Unit} {A : Ty Unit} (s : Subst UniverseSymbol Γ Δ)
    (t : Term UniverseSymbol Γ A) :
    (trTerm (HOL.subst s t) : CTm (Head L) Δ.length) =
      (trTerm t).subst (indexSub constName s) :=
  trWith_subst constName s t

/-- The term of an instance, in the logic of the sets, is the term of the body with the term
of the argument for its newest variable. -/
theorem trTerm_instantiate {Γ : Ctx Unit} {σ A : Ty Unit} (t : Term UniverseSymbol Γ σ)
    (body : Term UniverseSymbol (σ :: Γ) A) :
    (trTerm (HOL.instantiate t body) : CTm (Head L) Γ.length) =
      CTm.inst0 (trTerm t) (trTerm body) :=
  trWith_instantiate constName t body

end Commutation

variable [LevelOrder L]

/-! ## The rule constants in the judgment -/

section RuleJudgment

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverSetTheoryRules Q)

include covers

/-- The type of `impI` is a set. -/
theorem impIType_formed : CTyped Q Γ impIType allSets :=
  family_isSet covers.sets.contains (prop_isSet covers.sets)
    (family_isSet covers.sets.contains (prop_isSet covers.sets)
      (family_isSet covers.sets.contains
        (family_isSet covers.sets.contains (cHolds_isSet covers.sets (.var 1))
          (cHolds_isSet covers.sets (.var 1)))
        (cHolds_isSet covers.sets (cImp_typed covers.sets (.var 2) (.var 1)))))

/-- `impI` has its type. -/
theorem impI_typed : CTyped Q Γ (.const impIN) impIType :=
  definition_typed (covers.declared rfl) (impIType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))


/-- The type of `impE` is a set. -/
theorem impEType_formed : CTyped Q Γ impEType allSets :=
  family_isSet covers.sets.contains (prop_isSet covers.sets)
    (family_isSet covers.sets.contains (prop_isSet covers.sets)
      (family_isSet covers.sets.contains
        (cHolds_isSet covers.sets (cImp_typed covers.sets (.var 1) (.var 0)))
        (family_isSet covers.sets.contains (cHolds_isSet covers.sets (.var 2))
          (cHolds_isSet covers.sets (.var 2)))))

/-- `impE` has its type. -/
theorem impE_typed : CTyped Q Γ (.const impEN) impEType :=
  definition_typed (covers.declared rfl) (impEType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- The type of `allI` is formed, one universe above `allClasses`. -/
theorem allIType_formed :
    CTyped Q Γ allIType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.sets.contains.headTyping (.sort _)))
    (covers.sets.contains.isUniverse (.sort _))
    (classToClass_typed covers.sets.contains
      (classToClass_typed covers.sets.contains (.var 0) (prop_isClass covers.sets))
      (classToClass_typed covers.sets.contains
        (classToClass_typed covers.sets.contains (.var 1)
          (cHolds_isClass covers (.appElim (B := cProp) (.var 1) (.var 0))))
        (cHolds_isClass covers (cAll_typed covers.sets (.var 2) (.var 1)))))
    (covers.sets.contains.isUniverse (.sort _)) (covers.sets.contains.join (.sorts _ _))

/-- `allI` has its type. -/
theorem allI_typed : CTyped Q Γ (.const allIN) allIType :=
  definition_typed (covers.declared rfl) (allIType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- The type of `allE` is formed, one universe above `allClasses`. -/
theorem allEType_formed :
    CTyped Q Γ allEType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.sets.contains.headTyping (.sort _)))
    (covers.sets.contains.isUniverse (.sort _))
    (classToClass_typed covers.sets.contains
      (classToClass_typed covers.sets.contains (.var 0) (prop_isClass covers.sets))
      (classToClass_typed covers.sets.contains
        (cHolds_isClass covers (cAll_typed covers.sets (.var 1) (.var 0)))
        (classToClass_typed covers.sets.contains (.var 2)
          (cHolds_isClass covers (.appElim (B := cProp) (.var 2) (.var 0))))))
    (covers.sets.contains.isUniverse (.sort _)) (covers.sets.contains.join (.sorts _ _))

/-- `allE` has its type. -/
theorem allE_typed : CTyped Q Γ (.const allEN) allEType :=
  definition_typed (covers.declared rfl) (allEType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- The type of `eqI` is formed, one universe above `allClasses`. -/
theorem eqIType_formed :
    CTyped Q Γ eqIType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.sets.contains.headTyping (.sort _)))
    (covers.sets.contains.isUniverse (.sort _))
    (classToClass_typed covers.sets.contains (.var 0)
      (classToClass_typed covers.sets.contains (.var 1)
        (classToClass_typed covers.sets.contains
          (.idForm (u := .sort (.const (.above 1))) (.var 2)
            (covers.sets.contains.isUniverse (.sort _)) (.var 1) (.var 0))
          (cHolds_isClass covers (cEq_typed covers.sets (.var 3) (.var 2) (.var 1))))))
    (covers.sets.contains.isUniverse (.sort _)) (covers.sets.contains.join (.sorts _ _))

/-- `eqI` has its type. -/
theorem eqI_typed : CTyped Q Γ (.const eqIN) eqIType :=
  definition_typed (covers.declared rfl) (eqIType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- The type of `eqE` is formed, one universe above `allClasses`. -/
theorem eqEType_formed :
    CTyped Q Γ eqEType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.sets.contains.headTyping (.sort _)))
    (covers.sets.contains.isUniverse (.sort _))
    (classToClass_typed covers.sets.contains (.var 0)
      (classToClass_typed covers.sets.contains (.var 1)
        (classToClass_typed covers.sets.contains
          (cHolds_isClass covers (cEq_typed covers.sets (.var 2) (.var 1) (.var 0)))
          (.idForm (u := .sort (.const (.above 1))) (.var 3)
            (covers.sets.contains.isUniverse (.sort _)) (.var 2) (.var 1)))))
    (covers.sets.contains.isUniverse (.sort _)) (covers.sets.contains.join (.sorts _ _))

/-- `eqE` has its type. -/
theorem eqE_typed : CTyped Q Γ (.const eqEN) eqEType :=
  definition_typed (covers.declared rfl) (eqEType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- `the A x p` at variables: in the context of a set `A`, a set `x` and a proof that `x` is
a member of `A`, it is a term of `A`. -/
theorem theVars_typed :
    CTyped Q (.snoc (.snoc (.snoc Γ allSets) allSets) (cHolds (cIn (.var 0) (.var 1))))
      (cThe (.var 2) (.var 1) (.var 0)) (.var 2) :=
  .appElim (B := .var 3)
    (.appElim (B := .pi (cHolds (cIn (.var 0) (.var 3))) (.var 4))
      (.appElim (B := .pi allSets (.pi (cHolds (cIn (.var 0) (.var 1))) (.var 2)))
        (theConst_typed covers.sets) (.var 2)) (.var 1)) (.var 0)

/-- The type of `elemTheLaw` is a type of `allClasses`. -/
theorem elemTheLawType_formed : CTyped Q Γ elemTheLawType allClasses :=
  classToClass_typed covers.sets.contains (sets_typed covers.sets.contains)
    (classToClass_typed covers.sets.contains (sets_typed covers.sets.contains)
      (classToClass_typed covers.sets.contains
        (cHolds_isClass covers (cIn_typed covers.sets (.var 0) (.var 1)))
        (.idForm (u := .sort (.const (.above 1))) (sets_typed covers.sets.contains)
          (covers.sets.contains.isUniverse (.sort _))
          (elem_typed covers.sets (.var 2) (theVars_typed covers)) (.var 1))))

/-- `elemTheLaw` has its type. -/
theorem elemTheLaw_typed : CTyped Q Γ (.const elemTheLawN) elemTheLawType :=
  definition_typed (covers.declared rfl) (elemTheLawType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- `the A (elem A a) q` at variables: in the context of a set `A`, a term `a` of it and a
proof that `a`, as a set, is a member of `A`, it is a term of `A`. -/
theorem theElemVars_typed :
    CTyped Q (.snoc (.snoc (.snoc Γ allSets) (.var 0))
        (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))))
      (cThe (.var 2) (cElem (.var 2) (.var 1)) (.var 0)) (.var 2) :=
  .appElim (B := .var 3)
    (.appElim (B := .pi (cHolds (cIn (.var 0) (.var 3))) (.var 4))
      (.appElim (B := .pi allSets (.pi (cHolds (cIn (.var 0) (.var 1))) (.var 2)))
        (theConst_typed covers.sets) (.var 2)) (elem_typed covers.sets (.var 2) (.var 1)))
    (.var 0)

/-- The type of `theElemLaw` is a type of `allClasses`. -/
theorem theElemLawType_formed : CTyped Q Γ theElemLawType allClasses :=
  classToSet_typed covers.sets.contains (sets_typed covers.sets.contains)
    (family_isSet covers.sets.contains (.var 0)
      (family_isSet covers.sets.contains
        (cHolds_isSet covers.sets
          (cIn_typed covers.sets (elem_typed covers.sets (.var 1) (.var 0)) (.var 1)))
        (.idForm (u := .sort (.const (.above 0))) (.var 2)
          (covers.sets.contains.isUniverse (.sort _)) (theElemVars_typed covers) (.var 1))))

/-- `theElemLaw` has its type. -/
theorem theElemLaw_typed : CTyped Q Γ (.const theElemLawN) theElemLawType :=
  definition_typed (covers.declared rfl) (theElemLawType_formed covers)
    (covers.sets.contains.isUniverse (.sort _))

/-- **`impI p q f` proves `imp p q`** when `f` is a function from the proofs of `p` to the
proofs of `q`. -/
theorem cImpI_typed {p q f : CTm (Head L) n} (hp : CTyped Q Γ p cProp)
    (hq : CTyped Q Γ q cProp) (hf : CTyped Q Γ f (.pi (cHolds p) (cHolds (q.rename wk)))) :
    CTyped Q Γ (cImpI p q f) (cHolds (cImp p q)) := by
  have first : CTyped Q Γ (.app (.const impIN) p)
      (.pi cProp (.pi (.pi (cHolds (p.rename wk)) (cHolds (.var 1)))
        (cHolds (cImp ((p.rename wk).rename wk) (.var 1))))) :=
    .appElim (B := .pi cProp (.pi (.pi (cHolds (.var 1)) (cHolds (.var 1)))
      (cHolds (cImp (.var 2) (.var 1))))) (impI_typed covers) hp
  have second := CDerivable.appElim first hq
  have same : CTm.inst0 q (.pi (.pi (cHolds (p.rename wk)) (cHolds (.var 1)))
        (cHolds (cImp ((p.rename wk).rename wk) (.var 1)))) =
      (.pi (.pi (cHolds p) (cHolds (q.rename wk))) (cHolds (cImp (p.rename wk) (q.rename wk))) :
        CTm (Head L) n) := by
    show CTm.pi (.pi (cHolds (CTm.inst0 q (p.rename wk))) (cHolds (q.rename wk)))
        (cHolds (cImp (CTm.subst (CTm.liftSub (CTm.subst0 q)) ((p.rename wk).rename wk))
          (q.rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same] at second
  have third := CDerivable.appElim second hf
  have back : CTm.inst0 f (cHolds (cImp (p.rename wk) (q.rename wk))) = cHolds (cImp p q) := by
    show cHolds (cImp (CTm.inst0 f (p.rename wk)) (CTm.inst0 f (q.rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  rwa [back] at third

/-- **`impE p q h a` proves `q`** from a proof `h` of `imp p q` and a proof `a` of `p`. -/
theorem cImpE_typed {p q h a : CTm (Head L) n} (hp : CTyped Q Γ p cProp)
    (hq : CTyped Q Γ q cProp) (hh : CTyped Q Γ h (cHolds (cImp p q)))
    (ha : CTyped Q Γ a (cHolds p)) : CTyped Q Γ (cImpE p q h a) (cHolds q) := by
  have first : CTyped Q Γ (.app (.const impEN) p)
      (.pi cProp (.pi (cHolds (cImp (p.rename wk) (.var 0)))
        (.pi (cHolds ((p.rename wk).rename wk)) (cHolds (.var 2))))) :=
    .appElim (B := .pi cProp (.pi (cHolds (cImp (.var 1) (.var 0)))
      (.pi (cHolds (.var 2)) (cHolds (.var 2))))) (impE_typed covers) hp
  have second := CDerivable.appElim first hq
  have same : CTm.inst0 q (.pi (cHolds (cImp (p.rename wk) (.var 0)))
        (.pi (cHolds ((p.rename wk).rename wk)) (cHolds (.var 2)))) =
      (.pi (cHolds (cImp p q)) (.pi (cHolds (p.rename wk)) (cHolds ((q.rename wk).rename wk))) :
        CTm (Head L) n) := by
    show CTm.pi (cHolds (cImp (CTm.inst0 q (p.rename wk)) q))
        (.pi (cHolds (CTm.subst (CTm.liftSub (CTm.subst0 q)) ((p.rename wk).rename wk)))
          (cHolds ((q.rename wk).rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same] at second
  have third := CDerivable.appElim second hh
  have same' : CTm.inst0 h (.pi (cHolds (p.rename wk)) (cHolds ((q.rename wk).rename wk))) =
      (.pi (cHolds p) (cHolds (q.rename wk)) : CTm (Head L) n) := by
    show CTm.pi (cHolds (CTm.inst0 h (p.rename wk)))
        (cHolds (CTm.subst (CTm.liftSub (CTm.subst0 h)) ((q.rename wk).rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same'] at third
  have fourth := CDerivable.appElim third ha
  rwa [show CTm.inst0 a (cHolds (q.rename wk)) = cHolds q from congrArg cHolds
    (CTm.inst0_rename_wk a q)] at fourth

/-- **`allI T P f` proves `all T P`** when `f` gives a proof of `P x` at every `x` of `T`. -/
theorem cAllI_typed {T P f : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CTyped Q Γ P (.pi T cProp))
    (hf : CTyped Q Γ f (.pi T (cHolds (.app (P.rename wk) (.var 0))))) :
    CTyped Q Γ (cAllI T P f) (cHolds (cAll T P)) := by
  have first : CTyped Q Γ (.app (.const allIN) T)
      (.pi (.pi T cProp) (.pi (.pi (T.rename wk) (cHolds (.app (.var 1) (.var 0))))
        (cHolds (cAll ((T.rename wk).rename wk) (.var 1))))) :=
    .appElim (B := .pi (.pi (.var 0) cProp) (.pi (.pi (.var 1) (cHolds (.app (.var 1) (.var 0))))
      (cHolds (cAll (.var 2) (.var 1))))) (allI_typed covers) hT
  have second := CDerivable.appElim first hP
  have same : CTm.inst0 P (.pi (.pi (T.rename wk) (cHolds (.app (.var 1) (.var 0))))
        (cHolds (cAll ((T.rename wk).rename wk) (.var 1)))) =
      (.pi (.pi T (cHolds (.app (P.rename wk) (.var 0))))
        (cHolds (cAll (T.rename wk) (P.rename wk))) : CTm (Head L) n) := by
    show CTm.pi (.pi (CTm.inst0 P (T.rename wk))
          (cHolds (.app (P.rename wk) (.var 0))))
        (cHolds (cAll (CTm.subst (CTm.liftSub (CTm.subst0 P)) ((T.rename wk).rename wk))
          (P.rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same] at second
  have third := CDerivable.appElim second hf
  have back : CTm.inst0 f (cHolds (cAll (T.rename wk) (P.rename wk))) = cHolds (cAll T P) := by
    show cHolds (cAll (CTm.inst0 f (T.rename wk)) (CTm.inst0 f (P.rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  rwa [back] at third

/-- **`allE T P h t` proves `P t`** from a proof `h` of `all T P` and a term `t` of `T`. -/
theorem cAllE_typed {T P h t : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CTyped Q Γ P (.pi T cProp)) (hh : CTyped Q Γ h (cHolds (cAll T P)))
    (ht : CTyped Q Γ t T) : CTyped Q Γ (cAllE T P h t) (cHolds (.app P t)) := by
  have first : CTyped Q Γ (.app (.const allEN) T)
      (.pi (.pi T cProp) (.pi (cHolds (cAll (T.rename wk) (.var 0)))
        (.pi ((T.rename wk).rename wk) (cHolds (.app (.var 2) (.var 0)))))) :=
    .appElim (B := .pi (.pi (.var 0) cProp) (.pi (cHolds (cAll (.var 1) (.var 0)))
      (.pi (.var 2) (cHolds (.app (.var 2) (.var 0)))))) (allE_typed covers) hT
  have second := CDerivable.appElim first hP
  have same : CTm.inst0 P (.pi (cHolds (cAll (T.rename wk) (.var 0)))
        (.pi ((T.rename wk).rename wk) (cHolds (.app (.var 2) (.var 0))))) =
      (.pi (cHolds (cAll T P))
        (.pi (T.rename wk) (cHolds (.app ((P.rename wk).rename wk) (.var 0)))) :
        CTm (Head L) n) := by
    show CTm.pi (cHolds (cAll (CTm.inst0 P (T.rename wk)) P))
        (.pi (CTm.subst (CTm.liftSub (CTm.subst0 P)) ((T.rename wk).rename wk))
          (cHolds (.app ((P.rename wk).rename wk) (.var 0)))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same] at second
  have third := CDerivable.appElim second hh
  have same' : CTm.inst0 h (.pi (T.rename wk) (cHolds (.app ((P.rename wk).rename wk) (.var 0)))) =
      (.pi T (cHolds (.app (P.rename wk) (.var 0))) : CTm (Head L) n) := by
    show CTm.pi (CTm.inst0 h (T.rename wk))
        (cHolds (.app (CTm.subst (CTm.liftSub (CTm.subst0 h)) ((P.rename wk).rename wk))
          (.var 0))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk]
  rw [same'] at third
  have fourth := CDerivable.appElim third ht
  rwa [show CTm.inst0 t (cHolds (.app (P.rename wk) (.var 0))) = cHolds (.app P t) from by
    show cHolds (.app (CTm.inst0 t (P.rename wk)) t) = _
    rw [CTm.inst0_rename_wk]] at fourth

end RuleJudgment

/-! ## Presentations of the proofs -/

section Presentations

variable (L) in
/-- **A presentation of the proofs**: the terms that introduce and eliminate implication and
the universal quantifier. `impI p q b` proves `imp p q` from a body `b` under a proof of `p`;
`impE p q f a` proves `q` from `f` and `a`; `allI T φ b` proves `all T (λ T φ)` from a body `b`
under a variable of `T`; `allE T φ h t` proves the instance of `φ` at `t` from `h`. -/
structure ProofOps where
  /-- The introduction of an implication. -/
  impI : {n : Nat} → (p q : CTm (Head L) n) → (body : CTm (Head L) (n + 1)) → CTm (Head L) n
  /-- The elimination of an implication. -/
  impE : {n : Nat} → (p q f a : CTm (Head L) n) → CTm (Head L) n
  /-- The introduction of the universal quantifier. -/
  allI : {n : Nat} → (T : CTm (Head L) n) → (φ body : CTm (Head L) (n + 1)) → CTm (Head L) n
  /-- The elimination of the universal quantifier. -/
  allE : {n : Nat} → (T : CTm (Head L) n) → (φ : CTm (Head L) (n + 1)) →
    (h t : CTm (Head L) n) → CTm (Head L) n

variable {R' : Rules (Head L)}

/-- **The laws of a presentation in a package**: each of its four terms has the type of the
proofs of the conclusion of its rule, when its arguments are typed as the premises of the
rule. -/
structure ProofOps.Lawful (ops : ProofOps L) (Q : ChurchRules R') : Prop where
  /-- The introduction of an implication proves the implication. -/
  impI : ∀ {n : Nat} {Γ : CCtx (Head L) n} {p q : CTm (Head L) n} {b : CTm (Head L) (n + 1)},
    CTyped Q Γ p cProp → CTyped Q Γ q cProp →
    CTyped Q (.snoc Γ (cHolds p)) b (cHolds (q.rename wk)) →
      CTyped Q Γ (ops.impI p q b) (cHolds (cImp p q))
  /-- The elimination of an implication proves its conclusion. -/
  impE : ∀ {n : Nat} {Γ : CCtx (Head L) n} {p q f a : CTm (Head L) n},
    CTyped Q Γ p cProp → CTyped Q Γ q cProp →
    CTyped Q Γ f (cHolds (cImp p q)) → CTyped Q Γ a (cHolds p) →
      CTyped Q Γ (ops.impE p q f a) (cHolds q)
  /-- The introduction of the quantifier proves the quantification of the abstraction. -/
  allI : ∀ {n : Nat} {Γ : CCtx (Head L) n} {T : CTm (Head L) n} {φ b : CTm (Head L) (n + 1)},
    CTyped Q Γ T allClasses → CTyped Q (.snoc Γ T) φ cProp →
    CTyped Q (.snoc Γ T) b (cHolds φ) →
      CTyped Q Γ (ops.allI T φ b) (cHolds (cAll T (.lam T φ)))
  /-- The elimination of the quantifier proves the instance. -/
  allE : ∀ {n : Nat} {Γ : CCtx (Head L) n} {T : CTm (Head L) n} {φ : CTm (Head L) (n + 1)}
      {h t : CTm (Head L) n},
    CTyped Q Γ T allClasses → CTyped Q (.snoc Γ T) φ cProp →
    CTyped Q Γ h (cHolds (cAll T (.lam T φ))) → CTyped Q Γ t T →
      CTyped Q Γ (ops.allE T φ h t) (cHolds (CTm.inst0 t φ))

/-- **The presentation by the equations**: implication and the quantifier are introduced by
an abstraction and eliminated by an application. -/
def equationOps : ProofOps L where
  impI p _ body := .lam (cHolds p) body
  impE _ _ f a := .app f a
  allI T _ body := .lam T body
  allE _ _ h t := .app h t

/-- **The presentation by the rule constants**: `impI p q (λ (h : holds p). b)`,
`impE p q f a`, `allI T (λ T φ) (λ (x : T). b)` and `allE T (λ T φ) h t`. -/
def ruleOps : ProofOps L where
  impI p q body := cImpI p q (.lam (cHolds p) body)
  impE p q f a := cImpE p q f a
  allI T φ body := cAllI T (.lam T φ) (.lam T body)
  allE T φ h t := cAllE T (.lam T φ) h t

variable {Q : ChurchRules R'}

/-- **The laws of the presentation by the equations hold in every package over the set theory
that contains the steps of its equations**: the proofs of an implication are the functions
between the proofs (`holds_imp_rule`), and the proofs of a quantification of an abstraction
are the dependent functions into the proofs of its body (`holds_all_lam_rule`). -/
theorem equationOps_lawful (covers : OverSetTheory Q)
    (computes : StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q) :
    (equationOps (L := L)).Lawful Q where
  impI {_ _ p q _} hp hq hb :=
    .conv
      (.lamIntro (cHolds_typed covers hp) (covers.contains.isUniverse (.sort _))
        (smallFunctions_typed covers.contains (cHolds_typed covers hp)
          (cHolds_typed covers (hq.weaken (E := cHolds p))))
        (covers.contains.isUniverse (.sort _)) hb)
      (.symm (holds_imp_rule covers computes hp hq)) (covers.contains.isUniverse (.sort _))
  impE {_ _ _ q _ a} hp hq hf ha := by
    have applied := CDerivable.appElim
      (.conv hf (holds_imp_rule covers computes hp hq) (covers.contains.isUniverse (.sort _))) ha
    rwa [show CTm.inst0 a (cHolds (q.rename wk)) = cHolds q from
      congrArg cHolds (CTm.inst0_rename_wk _ _)] at applied
  allI hT hφ hb :=
    .conv
      (.lamIntro hT (covers.contains.isUniverse (.sort _))
        (classToSet_typed covers.contains hT (cHolds_isSet covers hφ))
        (covers.contains.isUniverse (.sort _)) hb)
      (.symm (holds_all_lam_rule covers computes hT hφ)) (covers.contains.isUniverse (.sort _))
  allE hT hφ hh ht :=
    .appElim
      (.conv hh (holds_all_lam_rule covers computes hT hφ) (covers.contains.isUniverse (.sort _)))
      ht

/-- **The laws of the presentation by the rule constants hold in every package that declares
them**, over the set theory: the abstractions are typed, and the instance is the β-step
between `(λ T φ) t` and `φ` at `t`. -/
theorem ruleOps_lawful (covers : OverSetTheoryRules Q) : (ruleOps (L := L)).Lawful Q where
  impI {_ _ p q _} hp hq hb :=
    cImpI_typed covers hp hq
      (.lamIntro (cHolds_typed covers.sets hp) (covers.sets.contains.isUniverse (.sort _))
        (smallFunctions_typed covers.sets.contains (cHolds_typed covers.sets hp)
          (cHolds_typed covers.sets (hq.weaken (E := cHolds p))))
        (covers.sets.contains.isUniverse (.sort _)) hb)
  impE hp hq hf ha := cImpE_typed covers hp hq hf ha
  allI {_ _ T φ _} hT hφ hb := by
    have predicate : CTyped Q _ (.lam T φ) (.pi T cProp) :=
      .lamIntro hT (covers.sets.contains.isUniverse (.sort _))
        (classToClass_typed covers.sets.contains hT (prop_isClass covers.sets))
        (covers.sets.contains.isUniverse (.sort _)) hφ
    have applied : CTyped Q (.snoc _ T) (.app ((CTm.lam T φ).rename wk) (.var 0)) cProp :=
      .appElim (B := cProp) (predicate.weaken (E := T)) (.var 0)
    have body : CTyped Q (.snoc _ T) _ (cHolds (.app ((CTm.lam T φ).rename wk) (.var 0))) :=
      .conv hb (.symm (cHolds_congr covers.sets (predicate_apply_var covers.sets hT hφ)))
        (covers.sets.contains.isUniverse (.sort _))
    exact cAllI_typed covers hT predicate
      (.lamIntro hT (covers.sets.contains.isUniverse (.sort _))
        (classToSet_typed covers.sets.contains hT (cHolds_isSet covers.sets applied))
        (covers.sets.contains.isUniverse (.sort _)) body)
  allE {_ _ T φ _ t} hT hφ hh ht := by
    have predicate : CTyped Q _ (.lam T φ) (.pi T cProp) :=
      .lamIntro hT (covers.sets.contains.isUniverse (.sort _))
        (classToClass_typed covers.sets.contains hT (prop_isClass covers.sets))
        (covers.sets.contains.isUniverse (.sort _)) hφ
    have beta : CEqual Q _ (.app (.lam T φ) t) (CTm.inst0 t φ) cProp :=
      .betaPi (B := cProp) (classToClass_typed covers.sets.contains hT (prop_isClass covers.sets))
        (covers.sets.contains.isUniverse (.sort _)) hφ ht
    exact .conv (cAllE_typed covers hT predicate hh ht) (cHolds_congr covers.sets beta)
      (covers.sets.contains.isUniverse (.sort _))

end Presentations

/-! ## Conversion is typed equality -/

section Conversion

variable {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
  {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)

variable (Q) in
/-- **The defining equations of the logic hold in a package** when, for each of them, the
terms of its two sides are equal there, at the term of its type and in the context of its
variables. -/
def EquationsHold (equations : List (HOL.DefiningEquation Const)) : Prop :=
  ∀ e ∈ equations, CEqual Q (ctxTm e.context) (trWith name e.left) (trWith name e.right)
    (tyTm e.type)

omit [LevelOrder L] in
/-- With no defining equation, nothing is asked: conversion is by β alone. -/
theorem equationsHold_nil : EquationsHold Q name ([] : List (HOL.DefiningEquation Const)) :=
  fun _ member => nomatch member

variable
  (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (name c)) (tyTm A))

include covers named

/-- **A substitution of terms of the logic for variables is a typed substitution of the
package.** -/
theorem indexSub_typed {Γ Δ : Ctx Unit} (s : Subst Const Γ Δ) :
    CSubstMor Q (ctxTm Γ) (ctxTm Δ) (indexSub name s) := by
  intro i
  obtain ⟨A, v, rfl⟩ := varIndex_surjective i
  rw [lookup_ctxTm, tyTm_subst, indexSub_varIndex]
  exact trWith_typed covers name named (s v)

/-- **A step of the conversion of the logic is a typed equality of the package**: β, an
instance of a defining equation that holds in the package, or either inside a term. -/
theorem trWith_sourceStep {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {τ : Ty Unit}
    {left right : Term Const Γ τ} (step : SourceStep equations left right) :
    CEqual Q (ctxTm Γ) (trWith name left) (trWith name right) (tyTm τ) := by
  induction step with
  | @beta Γ σ τ body argument =>
    have contracted := CDerivable.betaPi (B := tyTm τ) (tyTm_typed covers (.arr σ τ))
      (covers.contains.isUniverse (.sort _)) (trWith_typed covers name named body)
      (trWith_typed covers name named argument)
    rw [show CTm.inst0 (trWith name argument) (tyTm τ) = tyTm τ from tyTm_subst τ _,
      ← trWith_instantiate] at contracted
    exact contracted
  | @delta Γ equation listed substitution _ =>
    have instance' := (hold equation listed).substitute
      (indexSub_typed covers name named substitution)
    rw [tyTm_subst, ← trWith_subst, ← trWith_subst] at instance'
    exact instance'
  | @appFun Γ σ τ function function' argument _ ih =>
    have congruence := CDerivable.appCong ih (.refl (trWith_typed covers name named argument))
    rwa [show CTm.inst0 (trWith name argument) (tyTm τ) = tyTm τ from tyTm_subst τ _]
      at congruence
  | @appArg Γ σ τ function argument argument' _ ih =>
    have congruence := CDerivable.appCong (.refl (trWith_typed covers name named function)) ih
    rwa [show CTm.inst0 (trWith name argument) (tyTm τ) = tyTm τ from tyTm_subst τ _]
      at congruence
  | @lam Γ σ τ body body' _ ih =>
    exact .lamCong (.refl (tyTm_typed covers σ)) (covers.contains.isUniverse (.sort _))
      (tyTm_typed covers (.arr σ τ)) (covers.contains.isUniverse (.sort _)) ih
  | impLeft right _ ih =>
    exact cImp_congr covers ih (.refl (trWith_typed covers name named right))
  | impRight left _ ih =>
    exact cImp_congr covers (.refl (trWith_typed covers name named left)) ih
  | @eqLeft Γ τ left left' right _ ih =>
    exact cEq_congr covers (tyTm_typed covers τ) ih (.refl (trWith_typed covers name named right))
  | @eqRight Γ τ left right right' _ ih =>
    exact cEq_congr covers (tyTm_typed covers τ) (.refl (trWith_typed covers name named left)) ih
  | @all Γ σ body body' _ ih =>
    exact cAll_lam_congr covers (tyTm_typed covers σ) ih

/-- **Conversion is typed equality**: terms of the logic related by β and by instances of
defining equations that hold in the package have equal terms, at the term of their type and
in the context of their variables. -/
theorem trWith_conversion {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {τ : Ty Unit}
    {left right : Term Const Γ τ} (conversion : CoreConversion equations left right) :
    CEqual Q (ctxTm Γ) (trWith name left) (trWith name right) (tyTm τ) := by
  induction conversion with
  | rel _ _ step => exact trWith_sourceStep covers name named hold step.2.2
  | refl term => exact .refl (trWith_typed covers name named term)
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ first second => exact .trans first second

/-- **The proofs of convertible statements are equal types.** -/
theorem holds_conversion {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {φ ψ : Formula Const Γ}
    (conversion : CoreConversion equations φ ψ) :
    CEqual Q (ctxTm Γ) (cHolds (trWith name φ)) (cHolds (trWith name ψ)) U0 :=
  cHolds_congr covers (trWith_conversion covers name named hold conversion)

/-- **Statements convertible by β alone are equal propositions of the package**, in the
context of their variables. -/
theorem trWith_betaConversion {Γ : Ctx Unit} {φ ψ : Formula Const Γ}
    (conversion : CoreConversion ([] : List (HOL.DefiningEquation Const)) φ ψ) :
    CEqual Q (ctxTm Γ) (trWith name φ) (trWith name ψ) cProp :=
  trWith_conversion covers name named (equationsHold_nil name) conversion

/-- The proofs of statements convertible by β alone are equal types. -/
theorem holds_betaConversion {Γ : Ctx Unit} {φ ψ : Formula Const Γ}
    (conversion : CoreConversion ([] : List (HOL.DefiningEquation Const)) φ ψ) :
    CEqual Q (ctxTm Γ) (cHolds (trWith name φ)) (cHolds (trWith name ψ)) U0 :=
  holds_conversion covers name named (equationsHold_nil name) conversion

end Conversion

/-! ## Every proof is a term -/

section Proofs

variable {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
  {ops : ProofOps L} (lawful : ops.Lawful Q)
  {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
  (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (name c)) (tyTm A))

omit [LevelOrder L] in
/-- A weakened list of hypotheses has as many hypotheses. -/
theorem length_weakenHyps {Γ : Ctx Unit} {σ : Ty Unit} (Δ : List (Formula Const Γ)) :
    (weakenHyps (σ := σ) Δ).length = Δ.length :=
  List.length_map ..

omit [LevelOrder L] in
/-- The hypothesis of a weakened list at an occurrence is the weakened hypothesis. -/
theorem get_weakenHyps {Γ : Ctx Unit} {σ : Ty Unit} (Δ : List (Formula Const Γ))
    (i : Fin (weakenHyps (σ := σ) Δ).length) :
    (weakenHyps (σ := σ) Δ).get i = HOL.weaken (Δ.get (i.cast (length_weakenHyps Δ))) := by
  have h : weakenHyps (σ := σ) Δ = Δ.map (HOL.weaken (σ := σ)) := rfl
  rw [List.get_of_eq h, List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

variable (ops) in
/-- **The term of a proof of the logic, in a presentation of the proofs.** The variables of
the logic are placed at variables of the package by `ρ`, and each hypothesis is given a term.
A hypothesis is its term; the introduction and the elimination of implication and of the
universal quantifier are the four operations of the presentation, at the placed terms of the
statements, the terms of the subproofs and the placed term of the instance; a conversion
leaves the term as it is. -/
def trProof {equations : List (HOL.DefiningEquation Const)} :
    {Γ : Ctx Unit} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
      ProofSyntaxModulo equations Δ φ → {m : Nat} → Ren Γ.length m →
        (Fin Δ.length → CTm (Head L) m) → CTm (Head L) m
  | _, _, _, .hyp occurrence, _, _, hyps => hyps occurrence
  | _, _, _, @ProofSyntaxModulo.impI _ _ _ _ _ φ ψ body, _, ρ, hyps =>
      ops.impI ((trWith name φ).rename ρ) ((trWith name ψ).rename ρ)
        (trProof body (fun i => wk (ρ i)) (Fin.cases (.var 0) fun i => (hyps i).rename wk))
  | _, _, _, @ProofSyntaxModulo.impE _ _ _ _ _ φ ψ function argument, _, ρ, hyps =>
      ops.impE ((trWith name φ).rename ρ) ((trWith name ψ).rename ρ) (trProof function ρ hyps)
        (trProof argument ρ hyps)
  | _, Δ, _, @ProofSyntaxModulo.allI _ _ _ _ _ σ φ body, _, ρ, hyps =>
      ops.allI (tyTm σ) ((trWith name φ).rename (liftRen ρ))
        (trProof body (liftRen ρ) fun i => (hyps (i.cast (length_weakenHyps Δ))).rename wk)
  | _, _, _, @ProofSyntaxModulo.allE _ _ _ _ _ σ φ term function, _, ρ, hyps =>
      ops.allE (tyTm σ) ((trWith name φ).rename (liftRen ρ)) (trProof function ρ hyps)
        ((trWith name term).rename ρ)
  | _, _, _, .convert _ proof, _, ρ, hyps => trProof proof ρ hyps

include covers named in
/-- The term of a term of the logic, with its variables placed in a context of the package,
has the term of its type there. -/
theorem trWith_placed {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) {m : Nat}
    {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m} (placed : CCtxRen (ctxTm Γ) Θ ρ) :
    CTyped Q Θ ((trWith name t).rename ρ) (tyTm A) := by
  have typed := (trWith_typed covers name named t).rename placed
  rwa [tyTm_rename] at typed

omit [LevelOrder L] in
/-- A placement of the variables of the logic extends to one more variable of the logic,
placed at a new variable of the package. -/
theorem placement_lift {Γ : Ctx Unit} {m : Nat} {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m}
    (placed : CCtxRen (ctxTm Γ) Θ ρ) (σ : Ty Unit) :
    CCtxRen (ctxTm (σ :: Γ)) (.snoc Θ (tyTm σ)) (liftRen ρ) := by
  have lifted := placed.snoc (tyTm σ)
  rwa [tyTm_rename] at lifted

omit [LevelOrder L] in
/-- The placed term of a universal statement. -/
theorem trWith_all_rename {Γ : Ctx Unit} {σ : Ty Unit} (φ : Formula Const (σ :: Γ)) {m : Nat}
    (ρ : Ren Γ.length m) :
    ((trWith name (Term.all φ)).rename ρ : CTm (Head L) m) =
      cAll (tyTm σ) (.lam (tyTm σ) ((trWith name φ).rename (liftRen ρ))) := by
  show cAll ((tyTm σ).rename ρ) (.lam ((tyTm σ).rename ρ) ((trWith name φ).rename (liftRen ρ))) =
    _
  rw [tyTm_rename]

include covers lawful named in
/-- **Every proof of the logic is a term of the package.** In every package over the set
theory, for every presentation of the proofs whose laws hold there, and in which the defining
equations of the logic hold: for a context `Θ` of the package, a placement `ρ` of the
variables of the logic at variables of `Θ` of the terms of their types, and for each
hypothesis a term of `Θ` of the type of the proofs of its placed term, the term of a proof has
the type of the proofs of the placed term of its conclusion. -/
theorem trProof_typed {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntaxModulo equations Δ φ) :
    ∀ {m : Nat} {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m}, CCtxRen (ctxTm Γ) Θ ρ →
      ∀ {hyps : Fin Δ.length → CTm (Head L) m},
        (∀ i, CTyped Q Θ (hyps i) (cHolds ((trWith name (Δ.get i)).rename ρ))) →
          CTyped Q Θ (trProof ops name proof ρ hyps) (cHolds ((trWith name φ).rename ρ)) := by
  induction proof with
  | hyp occurrence => exact fun _ _ proved => proved occurrence
  | @impI Γ Δ φ ψ body ih =>
    intro m Θ ρ placed hyps proved
    have premise : CTyped Q Θ ((trWith name φ).rename ρ) cProp :=
      trWith_placed covers name named φ placed
    have conclusion : CTyped Q Θ ((trWith name ψ).rename ρ) cProp :=
      trWith_placed covers name named ψ placed
    have inner := ih (placement_succ placed (cHolds ((trWith name φ).rename ρ)))
      (hyps := Fin.cases (.var 0) fun i => (hyps i).rename wk)
      (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · show CTyped Q _ (.var 0) (cHolds ((trWith name φ).rename fun i => wk (ρ i)))
          rw [← CTm.rename_comp wk ρ]
          exact CDerivable.var (P := Q) (Γ := .snoc Θ (cHolds ((trWith name φ).rename ρ))) 0
        · show CTyped Q _ ((hyps j).rename wk)
            (cHolds ((trWith name (Δ.get j)).rename fun i => wk (ρ i)))
          rw [← CTm.rename_comp wk ρ]
          exact (proved j).weaken (E := cHolds ((trWith name φ).rename ρ)))
    rw [← CTm.rename_comp wk ρ] at inner
    exact lawful.impI premise conclusion inner
  | @impE Γ Δ φ ψ function argument ihFunction ihArgument =>
    intro m Θ ρ placed hyps proved
    exact lawful.impE (trWith_placed covers name named φ placed)
      (trWith_placed covers name named ψ placed) (ihFunction placed proved)
      (ihArgument placed proved)
  | @allI Γ Δ σ φ body ih =>
    intro m Θ ρ placed hyps proved
    have statement : CTyped Q (.snoc Θ (tyTm σ)) ((trWith name φ).rename (liftRen ρ)) cProp :=
      trWith_placed covers name named φ (placement_lift placed σ)
    have inner := ih (placement_lift placed σ)
      (hyps := fun i => (hyps (i.cast (length_weakenHyps Δ))).rename wk)
      (fun i => by
        rw [get_weakenHyps, trWith_weaken, CTm.rename_liftRen_wk]
        exact (proved (i.cast (length_weakenHyps Δ))).weaken (E := tyTm σ))
    rw [trWith_all_rename]
    exact lawful.allI (tyTm_typed covers σ) statement inner
  | @allE Γ Δ σ φ term function ih =>
    intro m Θ ρ placed hyps proved
    have statement : CTyped Q (.snoc Θ (tyTm σ)) ((trWith name φ).rename (liftRen ρ)) cProp :=
      trWith_placed covers name named φ (placement_lift placed σ)
    have universal := ih placed proved
    rw [trWith_all_rename] at universal
    rw [trWith_instantiate, CTm.rename_inst0]
    exact lawful.allE (tyTm_typed covers σ) statement universal
      (trWith_placed covers name named term placed)
  | @convert Γ Δ φ ψ conversion proof ih =>
    intro m Θ ρ placed hyps proved
    exact .conv (ih placed proved)
      (cHolds_congr covers ((trWith_conversion covers name named hold conversion).rename placed))
      (covers.contains.isUniverse (.sort _))

end Proofs

/-! ## Hypotheses at variables, and the context of a sequent -/

section Sequent

variable {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
  {ops : ProofOps L} (lawful : ops.Lawful Q)
  {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
  (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (name c)) (tyTm A))

include covers lawful named in
/-- **Every proof is a term, with its hypotheses at variables**: for a placement of the
variables of the logic and a placement of the hypotheses at variables of the context whose
types are the types of the proofs of their placed terms. -/
theorem trProof_typed_at {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntaxModulo equations Δ φ) {m : Nat}
    {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m} (placed : CCtxRen (ctxTm Γ) Θ ρ)
    (spot : Fin Δ.length → Fin m)
    (assumed : ∀ i, Θ.lookup (spot i) = cHolds ((trWith name (Δ.get i)).rename ρ)) :
    CTyped Q Θ (trProof ops name proof ρ fun i => .var (spot i))
      (cHolds ((trWith name φ).rename ρ)) :=
  trProof_typed covers lawful name named hold proof placed fun i =>
    assumed i ▸ CDerivable.var (spot i)

/-- The place of the variables of a sequent in its context: before the hypotheses. -/
def sequentRen {Γ : Ctx Unit} :
    (Δ : List (Formula Const Γ)) → Ren Γ.length (Γ.length + Δ.length)
  | [] => idRen
  | _ :: Δ => fun i => wk (sequentRen Δ i)

/-- The place of the hypotheses of a sequent in its context: the first hypothesis is the
newest variable. -/
def sequentSpot {Γ : Ctx Unit} :
    (Δ : List (Formula Const Γ)) → Fin Δ.length → Fin (Γ.length + Δ.length)
  | [], i => i.elim0
  | _ :: Δ, i =>
    Fin.cases (0 : Fin (Γ.length + Δ.length + 1)) (fun j => wk (sequentSpot Δ j)) i

/-- **The context of a sequent**: the terms of the types of its variables, followed by the
types of the proofs of its hypotheses. -/
def sequentCtx {Γ : Ctx Unit} :
    (Δ : List (Formula Const Γ)) → CCtx (Head L) (Γ.length + Δ.length)
  | [] => ctxTm Γ
  | δ :: Δ => .snoc (sequentCtx Δ) (cHolds ((trWith name δ).rename (sequentRen Δ)))

omit [LevelOrder L] in
/-- The variables of a sequent are placed in its context at the terms of their types. -/
theorem sequent_placed {Γ : Ctx Unit} : ∀ Δ : List (Formula Const Γ),
    CCtxRen (ctxTm Γ) (sequentCtx (L := L) name Δ) (sequentRen Δ)
  | [] => fun _ => (CTm.rename_id _).symm
  | _ :: Δ => placement_succ (sequent_placed Δ) _

omit [LevelOrder L] in
/-- The hypotheses of a sequent are placed in its context at the types of the proofs of their
terms. -/
theorem sequent_assumed {Γ : Ctx Unit} : ∀ (Δ : List (Formula Const Γ)) (i : Fin Δ.length),
    (sequentCtx (L := L) name Δ).lookup (sequentSpot Δ i) =
      cHolds ((trWith name (Δ.get i)).rename (sequentRen Δ))
  | [], i => i.elim0
  | δ :: Δ, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · show (cHolds ((trWith name δ).rename (sequentRen Δ))).rename wk =
        cHolds ((trWith name δ).rename fun i => wk (sequentRen Δ i))
      rw [← CTm.rename_comp wk (sequentRen Δ)]
      rfl
    · show ((sequentCtx (L := L) name Δ).lookup (sequentSpot Δ j)).rename wk =
        cHolds ((trWith name (Δ.get j)).rename fun i => wk (sequentRen Δ i))
      rw [sequent_assumed Δ j, ← CTm.rename_comp wk (sequentRen Δ)]
      rfl

include covers lawful named in
/-- **Every proof is a term in the context of its sequent**: in the context of the terms of
the types of its variables followed by the types of the proofs of its hypotheses, the term of
a proof, with each hypothesis as its variable, has the type of the proofs of the term of its
conclusion. -/
theorem trProof_sequent_typed {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntaxModulo equations Δ φ) :
    CTyped Q (sequentCtx name Δ)
      (trProof ops name proof (sequentRen Δ) fun i => .var (sequentSpot Δ i))
      (cHolds ((trWith name φ).rename (sequentRen Δ))) :=
  trProof_typed_at covers lawful name named hold proof (sequent_placed name Δ)
    (sequentSpot Δ) (sequent_assumed name Δ)

end Sequent

/-! ## Closed proofs -/

section Closed

variable {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
  {ops : ProofOps L} (lawful : ops.Lawful Q)
  {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
  (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (name c)) (tyTm A))

include covers lawful named in
/-- **A closed proof is a closed term**: with a closed term of the type of the proofs of each
hypothesis, the term of a closed proof has the type of the proofs of its conclusion. -/
theorem trProof_closed_typed {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} (proof : ProofSyntaxModulo equations Δ φ)
    {hyps : Fin Δ.length → CTm (Head L) 0}
    (proved : ∀ i, CTyped Q .nil (hyps i) (cHolds (trWith name (Δ.get i)))) :
    CTyped Q .nil (trProof ops name proof idRen hyps) (cHolds (trWith name φ)) := by
  have typed := trProof_typed covers lawful name named hold proof (Θ := .nil) (ρ := idRen)
    (fun i => i.elim0) (hyps := hyps) (fun i => by
      rw [CTm.rename_id]
      exact proved i)
  rwa [CTm.rename_id] at typed

variable (Q) in
/-- **A closed statement of the logic has a proof in a package** when the type of the proofs
of its term has a closed term there. -/
def HasProof (φ : ClosedFormula Const) : Prop :=
  ∃ t : CTm (Head L) 0, CTyped Q .nil t (cHolds (trWith name φ))

omit [LevelOrder L] in
/-- Statements that have proofs have terms for their proofs, one for each occurrence in a
list. -/
theorem hasProof_terms : ∀ {Δ : List (ClosedFormula Const)}, (∀ δ ∈ Δ, HasProof Q name δ) →
    ∃ hyps : Fin Δ.length → CTm (Head L) 0,
      ∀ i, CTyped Q .nil (hyps i) (cHolds (trWith name (Δ.get i)))
  | [], _ => ⟨Fin.elim0, fun i => i.elim0⟩
  | δ :: Δ, proved => by
    obtain ⟨first, typedFirst⟩ := proved δ List.mem_cons_self
    obtain ⟨rest, typedRest⟩ := hasProof_terms (Δ := Δ) fun δ' member =>
      proved δ' (List.mem_cons_of_mem _ member)
    exact ⟨Fin.cases first rest, fun i => Fin.cases typedFirst typedRest i⟩

include covers lawful named in
/-- **What is proved from statements that have proofs has a proof.** -/
theorem hasProof_of_proof {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} (proved : ∀ δ ∈ Δ, HasProof Q name δ)
    (proof : ProofSyntaxModulo equations Δ φ) : HasProof Q name φ := by
  obtain ⟨hyps, typed⟩ := hasProof_terms name proved
  exact ⟨_, trProof_closed_typed covers lawful name named hold proof typed⟩

end Closed

/-! ## The connectives -/

section Expansion

variable {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
  {ops : ProofOps L} (lawful : ops.Lawful Q)
  {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
  (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (name c)) (tyTm A))

omit [LevelOrder L] in
/-- The term of a conjunction written with implication and quantification is the written
conjunction of the terms. -/
theorem trWith_conjunctionFormula {Γ : Ctx Unit} (p q : Formula Const Γ) :
    (trWith name (conjunctionFormula p q) : CTm (Head L) Γ.length) =
      cAnd (trWith name p) (trWith name q) := by
  show cAll cProp (.lam cProp (cImp (cImp (trWith name (HOL.weaken p))
    (cImp (trWith name (HOL.weaken q)) (.var 0))) (.var 0))) = _
  rw [trWith_weaken, trWith_weaken]
  rfl

omit [LevelOrder L] in
/-- The term of a disjunction written with implication and quantification is the written
disjunction of the terms. -/
theorem trWith_disjunctionFormula {Γ : Ctx Unit} (p q : Formula Const Γ) :
    (trWith name (disjunctionFormula p q) : CTm (Head L) Γ.length) =
      cOr (trWith name p) (trWith name q) := by
  show cAll cProp (.lam cProp (cImp (cImp (trWith name (HOL.weaken p)) (.var 0))
    (cImp (cImp (trWith name (HOL.weaken q)) (.var 0)) (.var 0)))) = _
  rw [trWith_weaken, trWith_weaken]
  rfl

omit [LevelOrder L] in
/-- The term of an existential statement written with implication and quantification. -/
theorem trWith_existentialInline {Γ : Ctx Unit} {σ : Ty Unit} (φ : Formula Const (σ :: Γ)) :
    (trWith name (existentialInline φ) : CTm (Head L) Γ.length) =
      cAll cProp (.lam cProp (cImp (cAll (tyTm σ) (.lam (tyTm σ)
        (cImp ((trWith name φ).rename (liftRen wk)) (.var 1)))) (.var 0))) := by
  show cAll cProp (.lam cProp (cImp (cAll (tyTm σ) (.lam (tyTm σ)
    (cImp (trWith name (HOL.rename (Rename.lift Rename.weaken) φ)) (.var 1)))) (.var 0))) = _
  rw [trWith_rename_of name φ (liftRen_agrees (ρ := Rename.weaken) (r := wk) fun _ => rfl)]

omit [LevelOrder L] in
/-- The term of the true statement written with implication and quantification is the written
truth. -/
theorem trWith_truth {Γ : Ctx Unit} :
    (trWith name (truth : Formula Const Γ) : CTm (Head L) Γ.length) = cTrue := rfl

omit [LevelOrder L] in
/-- The term of the false statement written with quantification is the written falsity. -/
theorem trWith_falsity {Γ : Ctx Unit} :
    (trWith name (falsity : Formula Const Γ) : CTm (Head L) Γ.length) = cFalse := rfl

/-- A term of the logic without the existential quantifier. -/
def ExFree : {Γ : Ctx Unit} → {A : Ty Unit} → Term Const Γ A → Prop
  | _, _, .var _ | _, _, .const _ | _, _, .top | _, _, .bot => True
  | _, _, .app f x => ExFree f ∧ ExFree x
  | _, _, .lam body | _, _, .all body | _, _, .not body => ExFree body
  | _, _, .and p q | _, _, .or p q | _, _, .imp p q | _, _, .eq p q => ExFree p ∧ ExFree q
  | _, _, .ex _ => False

omit [LevelOrder L] in
/-- **Without the existential quantifier, a term of the logic and the same term with its
connectives written out have the same term**: the written connectives of the package are the
definitions by implication and quantification. -/
theorem trWith_expandInline_eq {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    ExFree t → (trWith name t : CTm (Head L) Γ.length) = trWith name (expandInline t) := by
  induction t with
  | var v => exact fun _ => rfl
  | const c => exact fun _ => rfl
  | app f x ihf ihx => exact fun free => congrArg₂ CTm.app (ihf free.1) (ihx free.2)
  | @lam σ Γ τ body ih => exact fun free => congrArg (CTm.lam (tyTm σ)) (ih free)
  | top => exact fun _ => rfl
  | bot => exact fun _ => rfl
  | and p q ihp ihq =>
    intro free
    show cAnd (trWith name p) (trWith name q) =
      trWith name (conjunctionFormula (expandInline p) (expandInline q))
    rw [trWith_conjunctionFormula, ← ihp free.1, ← ihq free.2]
  | or p q ihp ihq =>
    intro free
    show cOr (trWith name p) (trWith name q) =
      trWith name (disjunctionFormula (expandInline p) (expandInline q))
    rw [trWith_disjunctionFormula, ← ihp free.1, ← ihq free.2]
  | imp p q ihp ihq =>
    exact fun free => congrArg₂ (fun a b => cImp a b) (ihp free.1) (ihq free.2)
  | not p ih => exact fun free => congrArg (fun a => cImp a cFalse) (ih free)
  | @eq Γ τ x y ihx ihy =>
    exact fun free => congrArg₂ (fun a b => cEq (tyTm τ) a b) (ihx free.1) (ihy free.2)
  | @all σ Γ p ih =>
    exact fun free => congrArg (fun a => cAll (tyTm σ) (.lam (tyTm σ) a)) (ih free)
  | ex p _ => exact fun free => free.elim

include covers named in
/-- **The term of a term of the logic is equal to the term of the same term with its
connectives written out** by implication and quantification. Truth, falsity, negation,
conjunction and disjunction have the same terms; an existential statement differs by the
application of its predicate to the bound variable. -/
theorem trWith_expandInline {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    CEqual Q (ctxTm Γ) (trWith name t) (trWith name (expandInline t)) (tyTm A) := by
  induction t with
  | var v => exact .refl (trWith_typed covers name named (.var v))
  | const c => exact .refl (trWith_typed covers name named (.const c))
  | @app Γ σ τ f x ihf ihx =>
    have congruence := CDerivable.appCong ihf ihx
    rwa [show CTm.inst0 (trWith name x) (tyTm τ) = tyTm τ from tyTm_subst τ _] at congruence
  | @lam σ Γ τ body ih =>
    exact .lamCong (.refl (tyTm_typed covers σ)) (covers.contains.isUniverse (.sort _))
      (tyTm_typed covers (.arr σ τ)) (covers.contains.isUniverse (.sort _)) ih
  | top => exact .refl (cTrue_typed covers)
  | bot => exact .refl (cFalse_typed covers)
  | and p q ihp ihq =>
    show CEqual Q _ (cAnd (trWith name p) (trWith name q))
      (trWith name (conjunctionFormula (expandInline p) (expandInline q))) cProp
    rw [trWith_conjunctionFormula]
    exact cAnd_congr covers ihp ihq
  | or p q ihp ihq =>
    show CEqual Q _ (cOr (trWith name p) (trWith name q))
      (trWith name (disjunctionFormula (expandInline p) (expandInline q))) cProp
    rw [trWith_disjunctionFormula]
    exact cOr_congr covers ihp ihq
  | imp p q ihp ihq => exact cImp_congr covers ihp ihq
  | not p ih => exact cImp_congr covers ih (.refl (cFalse_typed covers))
  | @eq Γ τ x y ihx ihy => exact cEq_congr covers (tyTm_typed covers τ) ihx ihy
  | @all σ Γ p ih => exact cAll_lam_congr covers (tyTm_typed covers σ) ih
  | @ex σ Γ p ih =>
    show CEqual Q _ (cEx (tyTm σ) (.lam (tyTm σ) (trWith name p)))
      (trWith name (existentialInline (expandInline p))) cProp
    rw [trWith_existentialInline]
    have written := cEx_lam_eq covers (tyTm_typed covers σ) (trWith_typed covers name named p) ih
    rwa [tyTm_rename] at written

include covers named in
/-- The proofs of a statement and of the same statement with its connectives written out are
equal types. -/
theorem holds_expandInline {Γ : Ctx Unit} (φ : Formula Const Γ) :
    CEqual Q (ctxTm Γ) (cHolds (trWith name φ)) (cHolds (trWith name (expandInline φ))) U0 :=
  cHolds_congr covers (trWith_expandInline covers name named φ)

include covers lawful named in
/-- **A proof of the sequent with its connectives written out is a term for the sequent**:
the hypotheses are given terms of the types of the proofs of their own terms, and the term of
the proof has the type of the proofs of the term of the conclusion. -/
theorem trProof_expanded_typed {equations : List (HOL.DefiningEquation Const)}
    (hold : EquationsHold Q name equations) {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo equations (Δ.map expandInline) (expandInline φ)) {m : Nat}
    {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m} (placed : CCtxRen (ctxTm Γ) Θ ρ)
    {hyps : Fin Δ.length → CTm (Head L) m}
    (proved : ∀ i, CTyped Q Θ (hyps i) (cHolds ((trWith name (Δ.get i)).rename ρ))) :
    CTyped Q Θ (trProof ops name proof ρ fun i => hyps (i.cast (List.length_map ..)))
      (cHolds ((trWith name φ).rename ρ)) := by
  have expanded := trProof_typed covers lawful name named hold proof placed
    (hyps := fun i => hyps (i.cast (List.length_map ..)))
    (fun i => by
      rw [List.get_eq_getElem, List.getElem_map]
      exact .conv (proved _)
        (cHolds_congr covers ((trWith_expandInline covers name named _).rename placed))
        (covers.contains.isUniverse (.sort _)))
  exact .conv expanded
    (.symm (cHolds_congr covers ((trWith_expandInline covers name named φ).rename placed)))
    (covers.contains.isUniverse (.sort _))

variable (ops) in
/-- **The term of a proof of the full calculus**: the term of its elaboration into the
calculus modulo conversion, in which the rules of the connectives are proofs by implication
and quantification. It is defined on the proofs that use the rules of hypotheses, of the
connectives and of the quantifiers. -/
def trFullProof? {Γ : Ctx Unit} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) {m : Nat} (ρ : Ren Γ.length m)
    (hyps : Fin Δ.length → CTm (Head L) m) : Option (CTm (Head L) m) :=
  (expandProofModulo? (eqs := ([] : List (HOL.DefiningEquation Const))) proof).map
    fun elaborated => trProof ops name elaborated ρ fun i => hyps (i.cast (List.length_map ..))

omit [LevelOrder L] in
variable (ops) in
/-- The term of a proof of the full calculus is defined exactly on the fragment of the
hypotheses, the connectives and the quantifiers. -/
theorem trFullProof?_isSome {Γ : Ctx Unit} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) {m : Nat} (ρ : Ren Γ.length m)
    (hyps : Fin Δ.length → CTm (Head L) m) :
    (trFullProof? ops name proof ρ hyps).isSome = connectiveFragment proof := by
  unfold trFullProof?
  rw [Option.isSome_map]
  exact expandProofModulo?_isSome proof

include covers lawful named in
/-- **A proof of the full calculus in the fragment of the connectives is a term for its
statement.** -/
theorem trFullProof?_typed {Γ : Ctx Unit} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) {m : Nat} {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m}
    (placed : CCtxRen (ctxTm Γ) Θ ρ) {hyps : Fin Δ.length → CTm (Head L) m}
    (proved : ∀ i, CTyped Q Θ (hyps i) (cHolds ((trWith name (Δ.get i)).rename ρ)))
    {t : CTm (Head L) m} (found : trFullProof? ops name proof ρ hyps = some t) :
    CTyped Q Θ t (cHolds ((trWith name φ).rename ρ)) := by
  obtain ⟨elaborated, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact trProof_expanded_typed covers lawful name named (equationsHold_nil name) elaborated
    placed proved

include covers lawful named in
/-- A proof of the full calculus in the fragment of the connectives has a term. -/
theorem trFullProof?_exists {Γ : Ctx Unit} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) (fragment : connectiveFragment proof = true) {m : Nat}
    {Θ : CCtx (Head L) m} {ρ : Ren Γ.length m} (placed : CCtxRen (ctxTm Γ) Θ ρ)
    {hyps : Fin Δ.length → CTm (Head L) m}
    (proved : ∀ i, CTyped Q Θ (hyps i) (cHolds ((trWith name (Δ.get i)).rename ρ))) :
    ∃ t, trFullProof? ops name proof ρ hyps = some t ∧
      CTyped Q Θ t (cHolds ((trWith name φ).rename ρ)) := by
  obtain ⟨t, found⟩ := Option.isSome_iff_exists.mp
    ((trFullProof?_isSome ops name proof ρ hyps).trans fragment)
  exact ⟨t, found, trFullProof?_typed covers lawful name named proof placed proved found⟩

include covers named in
/-- A closed statement has a proof exactly when the statement with its connectives written
out has one. -/
theorem hasProof_expandInline {φ : ClosedFormula Const} :
    HasProof Q name (expandInline φ) ↔ HasProof Q name φ :=
  ⟨fun ⟨t, typed⟩ => ⟨t, .conv typed (.symm (holds_expandInline covers name named φ))
      (covers.contains.isUniverse (.sort _))⟩,
    fun ⟨t, typed⟩ => ⟨t, .conv typed (holds_expandInline covers name named φ)
      (covers.contains.isUniverse (.sort _))⟩⟩

include covers lawful named in
/-- **What the full calculus proves, in the fragment of the connectives, from statements that
have proofs has a proof.** -/
theorem hasProof_of_fullProof {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (proved : ∀ δ ∈ Δ, HasProof Q name δ) (proof : ProofSyntax Const Δ φ)
    (fragment : connectiveFragment proof = true) : HasProof Q name φ := by
  obtain ⟨elaborated, _⟩ := Option.isSome_iff_exists.mp
    ((expandProofModulo?_isSome (eqs := ([] : List (HOL.DefiningEquation Const))) proof).trans
      fragment)
  refine (hasProof_expandInline covers name named).mp
    (hasProof_of_proof covers lawful name named (equationsHold_nil name) (fun δ member => ?_)
      elaborated)
  obtain ⟨source, among, rfl⟩ := List.mem_map.mp member
  exact (hasProof_expandInline covers name named).mpr (proved source among)

end Expansion

/-! ## Proofs from the eleven laws -/

section Laws

/-- The laws of the presentation by the equations hold in the package with the eleven
laws. -/
theorem setLaws_equationOps_lawful : (equationOps (L := L)).Lawful (setLaws L) :=
  equationOps_lawful (withProofs_over lawRows) (withProofs_computes lawRows)

/-- **Each of the eleven laws has a proof in the package with the laws**: its proof
constant. -/
theorem law_hasProof {φ : ClosedFormula UniverseSymbol} (law : φ ∈ universeTheory) :
    HasProof (setLaws L) constName φ := by
  have member : φ ∈ lawRows.map Prod.snd := lawRows_statements ▸ law
  obtain ⟨row, among, rfl⟩ := List.mem_map.mp member
  exact ⟨_, setLaws_typed row among⟩

/-- Each of the eleven laws with its connectives written out has a proof in the package with
the laws: the proof constant of the law. -/
theorem expandedLaw_hasProof {φ : ClosedFormula UniverseSymbol}
    (law : φ ∈ universeTheory.map expandInline) : HasProof (setLaws L) constName φ := by
  obtain ⟨source, among, rfl⟩ := List.mem_map.mp law
  exact (hasProof_expandInline (withProofs_over lawRows) constName
    (constName_typed (withProofs_over lawRows))).mpr (law_hasProof among)

/-- **A proof from the laws is a closed term of the package with the laws.** A closed proof
modulo conversion whose hypotheses are among the eleven laws, as written or with their
connectives written out, gives a closed term of the type of the proofs of its conclusion. -/
theorem lawProof_exists {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (setLaws L) constName equations)
    {Δ : List (ClosedFormula UniverseSymbol)} {φ : ClosedFormula UniverseSymbol}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline)
    (proof : ProofSyntaxModulo equations Δ φ) :
    ∃ t : CTm (Head L) 0, CTyped (setLaws L) .nil t (cHolds (trTerm φ)) :=
  hasProof_of_proof (withProofs_over lawRows) (setLaws_equationOps_lawful (L := L)) constName
    (constName_typed (withProofs_over lawRows)) hold
    (fun δ member => (among δ member).elim law_hasProof expandedLaw_hasProof) proof

/-- **A proof of the full calculus from the laws, by the rules of the hypotheses, the
connectives and the quantifiers, is a closed term of the package with the laws.** -/
theorem fullLawProof_exists {Δ : List (ClosedFormula UniverseSymbol)}
    {φ : ClosedFormula UniverseSymbol} (among : ∀ δ ∈ Δ, δ ∈ universeTheory)
    (proof : ProofSyntax UniverseSymbol Δ φ) (fragment : connectiveFragment proof = true) :
    ∃ t : CTm (Head L) 0, CTyped (setLaws L) .nil t (cHolds (trTerm φ)) :=
  hasProof_of_fullProof (withProofs_over lawRows) (setLaws_equationOps_lawful (L := L)) constName
    (constName_typed (withProofs_over lawRows)) (fun δ member => law_hasProof (among δ member))
    proof fragment

/-- The eleven laws have a proof constant each. -/
theorem lawRows_length : universeTheory.length = lawRows.length := rfl

/-- **The proof constants of the eleven laws**, in the order of the laws. -/
def lawConstants (i : Fin universeTheory.length) : CTm (Head L) 0 :=
  .const (lawRows.get (i.cast lawRows_length)).1

/-- The proof constant of a law has the type of the proofs of the law. -/
theorem lawConstants_typed (i : Fin universeTheory.length) :
    CTyped (setLaws L) .nil (lawConstants i) (cHolds (trTerm (universeTheory.get i))) := by
  have typed := setLaws_typed (L := L) (lawRows.get (i.cast lawRows_length)) (List.get_mem _ _)
  have same : (lawRows.get (i.cast lawRows_length)).2 = universeTheory.get i := by
    rw [List.get_of_eq lawRows_statements.symm i, List.get_eq_getElem, List.get_eq_getElem,
      List.getElem_map]
    rfl
  rw [same] at typed
  exact typed

/-- **The term of a proof from the eleven laws**: each hypothesis is discharged by the proof
constant of its law, and the term has the type of the proofs of the conclusion. -/
theorem lawProof_typed {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (setLaws L) constName equations) {φ : ClosedFormula UniverseSymbol}
    (proof : ProofSyntaxModulo equations universeTheory φ) :
    CTyped (setLaws L) .nil (trProof equationOps constName proof idRen lawConstants)
      (cHolds (trTerm φ)) :=
  trProof_closed_typed (withProofs_over lawRows) setLaws_equationOps_lawful constName
    (constName_typed (withProofs_over lawRows)) hold proof lawConstants_typed

/-- **The term of a proof from the eleven laws with their connectives written out**: each
hypothesis is discharged by the proof constant of its law, whose type of proofs is equal to
that of the law written out. -/
theorem expandedLawProof_typed {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (setLaws L) constName equations) {φ : ClosedFormula UniverseSymbol}
    (proof : ProofSyntaxModulo equations (universeTheory.map expandInline) φ) :
    CTyped (setLaws L) .nil
      (trProof equationOps constName proof idRen fun i =>
        lawConstants (i.cast (List.length_map ..)))
      (cHolds (trTerm φ)) :=
  trProof_closed_typed (withProofs_over lawRows) setLaws_equationOps_lawful constName
    (constName_typed (withProofs_over lawRows)) hold proof
    (hyps := fun i => lawConstants (i.cast (List.length_map ..))) fun i => by
      rw [List.get_eq_getElem, List.getElem_map]
      exact .conv (lawConstants_typed (i.cast (List.length_map ..)))
        (holds_expandInline (Γ := []) (withProofs_over lawRows) constName
          (constName_typed (withProofs_over lawRows))
          (universeTheory.get (i.cast (List.length_map ..))))
        ((withProofs_over (L := L) lawRows).contains.isUniverse (.sort _))

/-- **The term of a proof of the full calculus from the eleven laws**, by the rules of the
hypotheses, the connectives and the quantifiers, has the type of the proofs of the
conclusion. -/
theorem fullLawProof_typed {φ : ClosedFormula UniverseSymbol}
    (proof : ProofSyntax UniverseSymbol universeTheory φ) {t : CTm (Head L) 0}
    (found : trFullProof? equationOps constName proof idRen lawConstants = some t) :
    CTyped (setLaws L) .nil t (cHolds (trTerm φ)) := by
  have typed := trFullProof?_typed (withProofs_over lawRows) setLaws_equationOps_lawful
    constName (constName_typed (withProofs_over lawRows)) proof (Θ := .nil) (ρ := idRen)
    (fun i => i.elim0) (hyps := lawConstants) (fun i => by
      rw [CTm.rename_id]
      exact lawConstants_typed i) found
  rwa [CTm.rename_id] at typed

/-! ### What is proved is true -/

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large in
/-- **What has a proof in the package with the laws is true in the model of the logic**,
relative to cofinally many inaccessible cardinals in two universes. -/
theorem models_of_hasProof {φ : ClosedFormula UniverseSymbol}
    (proved : HasProof (setLaws L) constName φ) : (universeModel small).models φ := by
  obtain ⟨t, typed⟩ := proved
  by_contra false
  exact CDerivable.no_closed_inhabitant
    (setLaws_setModel small large (fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅))
    (notMem_holds_trTerm small large
      (reads_familyConsts _ _ fun c declared => by
        cases found : proofDecls L lawRows c with
        | none => exact absurd found declared
        | some T =>
          obtain ⟨ψ, member, -⟩ := proofDecls_some found
          exact lawRows_fresh _ member)
      false) t typed

include small large in
/-- **What the logic proves from the eleven laws, through the package, is true in the model of
the logic.** -/
theorem lawProof_sound {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (setLaws L) constName equations)
    {Δ : List (ClosedFormula UniverseSymbol)} {φ : ClosedFormula UniverseSymbol}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline)
    (proof : ProofSyntaxModulo equations Δ φ) : (universeModel small).models φ :=
  models_of_hasProof small large (lawProof_exists hold among proof)

/-! ### The empty set is a subset of every set -/

/-- **The empty set is a subset of every set**: `∀ x. ∀ y. y ∈ Empty → y ∈ x`. -/
def emptySubset : ClosedFormula UniverseSymbol :=
  .all (subsetFormula (.const (.core .empty)) (.var .vz))

/-- The law of the empty set with its negation written out: `∀ x. x ∈ Empty → ∀ r. r`. -/
theorem expandInline_emptyLaw :
    expandInline (embed emptyLaw) =
      .all (.imp (inSet (.var .vz) (.const (.core .empty))) falsity) := rfl

/-- The statement, written out: `∀ x. ∀ y. y ∈ Empty → y ∈ x`. -/
theorem emptySubset_eq :
    emptySubset = .all (.all (.imp (inSet (.var .vz) (.const (.core .empty)))
      (inSet (.var .vz) (.var (.vs .vz))))) := rfl

/-- **The proof, from the law of the empty set.** For sets `x` and `y` and a hypothesis that
`y` is a member of the empty set: the law at `y` and the hypothesis give falsity, and falsity
at the statement that `y` is a member of `x` gives that statement. -/
def emptySubsetProof :
    ProofSyntaxModulo ([] : List (HOL.DefiningEquation UniverseSymbol))
      [expandInline (embed emptyLaw)] emptySubset :=
  .allI (σ := .base ()) (.allI (σ := .base ()) (.impI
    (φ := inSet (.var .vz) (.const (.core .empty))) (ψ := inSet (.var .vz) (.var (.vs .vz)))
    (.allE (φ := .var .vz) (inSet (.var .vz) (.var (.vs .vz)))
      (.impE (φ := inSet (.var .vz) (.const (.core .empty))) (ψ := falsity)
        (.allE (φ := .imp (inSet (.var .vz) (.const (.core .empty))) falsity) (.var .vz)
          (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
            weakenHyps (weakenHyps [expandInline (embed emptyLaw)])) ⟨1, by decide⟩))
        (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
          weakenHyps (weakenHyps [expandInline (embed emptyLaw)])) ⟨0, by decide⟩)))))

/-- **The term of the proof**: `λ x y. λ h : holds (In y Empty). emptyLaw y h (In y x)`. By
the equations of the set theory, the proof constant of the law at `y` is a function from the
proofs of `In y Empty` to the proofs of falsity, and a proof of falsity is a function from the
propositions to their proofs. -/
def emptySubsetTerm : CTm (Head L) 0 :=
  .lam allSets (.lam allSets (.lam (cHolds (cIn (.var 0) cEmpty))
    (.app (.app (.app (.const emptyLawN) (.var 1)) (.var 0)) (cIn (.var 1) (.var 2)))))

omit [LevelOrder L] in
/-- The term of the proof, with the proof constant of the law for its hypothesis, is that
term. -/
theorem trProof_emptySubsetProof :
    trProof equationOps constName emptySubsetProof idRen (fun _ => .const emptyLawN) =
      (emptySubsetTerm : CTm (Head L) 0) := rfl

omit [LevelOrder L] in
/-- The term of the statement:
`all set (λ x. all set (λ y. imp (In y Empty) (In y x)))`. -/
theorem trTerm_emptySubset :
    (trTerm emptySubset : CTm (Head L) 0) =
      cAll allSets (.lam allSets (cAll allSets (.lam allSets
        (cImp (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1)))))) := rfl

/-- Positive example: **the empty set is a subset of every set, as a closed term of the
package with the laws**, of the type of the proofs of the statement. -/
theorem emptySubset_typed :
    CTyped (setLaws L) .nil emptySubsetTerm
      (cHolds (cAll allSets (.lam allSets (cAll allSets (.lam allSets
        (cImp (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1)))))))) :=
  trProof_closed_typed (withProofs_over lawRows) setLaws_equationOps_lawful constName
    (constName_typed (withProofs_over lawRows)) (equationsHold_nil constName) emptySubsetProof
    (hyps := fun _ => .const emptyLawN) fun i => match i with
      | ⟨0, _⟩ => emptyLaw_typed

/-- **The same statement in the full calculus, from the law of the empty set as written**, with
its negation. For sets `x` and `y` and a hypothesis that `y` is a member of the empty set: the
law at `y` and the hypothesis give falsity, by the rule of negation, and falsity gives the
statement that `y` is a member of `x`, by its rule. -/
def emptySubsetFullProof : ProofSyntax UniverseSymbol [embed emptyLaw] emptySubset :=
  .allI (σ := .base ()) (.allI (σ := .base ()) (.impI
    (φ := inSet (.var .vz) (.const (.core .empty))) (ψ := inSet (.var .vz) (.var (.vs .vz)))
    (.botE (φ := inSet (.var .vz) (.var (.vs .vz)))
      (.notE (φ := inSet (.var .vz) (.const (.core .empty)))
        (.allE (φ := .not (inSet (.var .vz) (.const (.core .empty)))) (.var .vz)
          (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
            weakenHyps (weakenHyps [embed emptyLaw])) ⟨1, by decide⟩))
        (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
          weakenHyps (weakenHyps [embed emptyLaw])) ⟨0, by decide⟩)))))

/-- That proof uses only the rules of the hypotheses, the connectives and the quantifiers. -/
theorem emptySubsetFullProof_fragment : connectiveFragment emptySubsetFullProof = true := rfl

omit [LevelOrder L] in
/-- Positive example: **the proof of the full calculus, from the law as written, has the same
term** as the proof from the law with its negation written out. -/
theorem trFullProof?_emptySubsetFullProof :
    trFullProof? equationOps constName emptySubsetFullProof idRen (fun _ => .const emptyLawN) =
      some (emptySubsetTerm : CTm (Head L) 0) := rfl

include small large in
/-- The statement that the empty set is a subset of every set is true in the model of the
logic: it has a proof in the package with the laws. -/
theorem emptySubset_true : (universeModel small).models emptySubset :=
  models_of_hasProof (L := Nat) small large ⟨_, emptySubset_typed⟩

/-! ### The empty set is not a member of itself -/

/-- The closed statement that the empty set is a member of itself. -/
def emptyInEmpty : ClosedFormula UniverseSymbol :=
  inSet (.const (.core .empty)) (.const (.core .empty))

omit [LevelOrder L] in
/-- The term of the statement that the empty set is a member of itself: `In Empty Empty`. -/
theorem trTerm_emptyInEmpty : (trTerm emptyInEmpty : CTm (Head L) 0) = cIn cEmpty cEmpty := rfl

include small large in
/-- The statement that the empty set is a member of itself has no proof in the package with
the laws, relative to cofinally many inaccessible cardinals in two universes. -/
theorem emptyInEmpty_no_hasProof : ¬ HasProof (setLaws L) constName emptyInEmpty :=
  fun ⟨t, typed⟩ => setLaws_consistent small large t typed

include small large in
/-- No proof of the logic from the eleven laws, modulo defining equations that hold in the
package with the laws, concludes that the empty set is a member of itself: such a proof would
be a closed term of the package. -/
theorem no_proof_emptyInEmpty_of_hold
    {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (setLaws L) constName equations)
    {Δ : List (ClosedFormula UniverseSymbol)}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline) :
    IsEmpty (ProofSyntaxModulo equations Δ emptyInEmpty) :=
  ⟨fun proof => emptyInEmpty_no_hasProof small large (lawProof_exists hold among proof)⟩

include small large in
/-- Negative example: **no proof of the logic from the eleven laws concludes that the empty
set is a member of itself**, relative to cofinally many inaccessible cardinals in two
universes: such a proof would be a closed term of the package with the laws, and there is
none. -/
theorem no_proof_emptyInEmpty {Δ : List (ClosedFormula UniverseSymbol)}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline) :
    IsEmpty (ProofSyntaxModulo ([] : List (HOL.DefiningEquation UniverseSymbol)) Δ
      emptyInEmpty) :=
  no_proof_emptyInEmpty_of_hold (L := Nat) small large (equationsHold_nil constName) among

include small large in
/-- Negative example: no proof of the full calculus from the eleven laws that concludes that
the empty set is a member of itself uses only the rules of the hypotheses, the connectives
and the quantifiers. -/
theorem no_fullProof_emptyInEmpty {Δ : List (ClosedFormula UniverseSymbol)}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory) (proof : ProofSyntax UniverseSymbol Δ emptyInEmpty) :
    connectiveFragment proof = false := by
  cases fragment : connectiveFragment proof with
  | false => rfl
  | true =>
    exact absurd (fullLawProof_exists (L := Nat) among proof fragment)
      (emptyInEmpty_no_hasProof small large)

end Laws

/-! ## Proofs on the rule constants

In the set theory on rule constants (`setTheoryRules`), the proofs are built by the presentation
of the rule constants (`ruleOps`): nothing unfolds the type of the proofs of a statement. -/

section RuleLaws

open ZFSetUniverseClosure (univOf)
open ZFSetUniverseLift (univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet)

/-- **Falsity has no closed proof in the set theory on rule constants**, relative to cofinally
many inaccessible cardinals in two universes: the elimination of the quantifier would make it
a proof that the empty set is a member of itself. -/
theorem setTheoryRules_no_proof_falsity (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (t : CTm (Head L) 0) :
    ¬ CTyped (setTheoryRules L) .nil t (cHolds cFalse) := fun typed =>
  setTheoryRules_consistent small large _
    ((ruleOps_lawful setTheoryRules_over).allE (prop_isClass setTheoryRules_over.sets) (.var 0)
      typed
      (cIn_typed setTheoryRules_over.sets (empty_typed setTheoryRules_over.sets)
        (empty_typed setTheoryRules_over.sets)))

variable (L) in
/-- **The set theory on rule constants with a proof constant for each of a list of named
closed statements**, and no equation. -/
abbrev withRuleProofs (rows : List (DeclName × ClosedFormula UniverseSymbol)) :=
  withRules L (proofTable L rows)

variable (L) in
/-- **The set theory on rule constants with the eleven laws**, each declared as a proof
constant. -/
abbrev ruleLaws := withRuleProofs L lawRows

/-- The package with the eleven laws on rule constants declares the constants of set theory
and the rule constants. -/
theorem ruleLaws_over : OverSetTheoryRules (ruleLaws L) := withRules_over _

/-- A proof constant of the table with the rules has its type: the type of the proofs of the
term of its statement. -/
theorem ruleProofConstant_typed {rows : List (DeclName × ClosedFormula UniverseSymbol)}
    {c : DeclName} {φ : ClosedFormula UniverseSymbol}
    (declared : tableLookup (rulesTable L (proofTable L rows)) c = some (cHolds (trTerm φ))) :
    CTyped (withRuleProofs L rows) .nil (.const c) (cHolds (trTerm φ)) := by
  have typed := definition_typed (Γ := (.nil : CCtx (Head L) 0))
    (withRules_declared.trans declared) (holds_trTerm_typed (withRules_over _).sets φ)
    ((withRules_over (L := L) (proofTable L rows)).sets.contains.isUniverse (.sort _))
  rwa [CTm.liftClosed_zero] at typed

/-- **Each proof constant of the package has the type of the proofs of its law.** -/
theorem ruleLaws_typed : ∀ row ∈ lawRows,
    CTyped (ruleLaws L) .nil (.const row.1) (cHolds (trTerm row.2)) := by
  intro row member
  simp only [lawRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ruleProofConstant_typed rfl

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- **The set theory on rule constants with proof constants for closed statements that are
true in the model of the logic has a set model**: the constants of set theory at their values,
every rule constant and every proof constant read as the empty set. -/
theorem withRuleProofs_setModel {rows : List (DeclName × ClosedFormula UniverseSymbol)}
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1})
    (valid : ∀ row ∈ rows, (universeModel small).models row.2) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (tableLookup (rulesTable L (proofTable L rows)))
        (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large)))
      (withRuleProofs L rows) :=
  withRules_setModel_of_agreeing (stages_closedChain small large) groundTyped
    (fun hx => univOf_mem_carrierCode small large hx) ν
    (fun consts reads {c T} member => by
      obtain ⟨⟨name, φ⟩, among, same⟩ := List.mem_map.mp member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact (empty_mem_holds_trTerm_iff small large reads φ).mpr (valid _ among))
    base _ fun _ _ => rfl

include small in
/-- **The package with the eleven laws on rule constants has a set model**, relative to
cofinally many inaccessible cardinals in two universes. -/
theorem ruleLaws_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (tableLookup (rulesTable L (proofTable L lawRows)))
        (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large)))
      (ruleLaws L) :=
  withRuleProofs_setModel small large ν groundTyped base (lawRows_valid small)

include small large in
/-- **Consistency of the package with the eleven laws on rule constants**, relative to
cofinally many inaccessible cardinals in two universes: no closed term proves that the empty
set is a member of itself. -/
theorem ruleLaws_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (ruleLaws L) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  CDerivable.no_closed_inhabitant
    (ruleLaws_setModel small large (fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅))
    (notMem_holds_empty_in_empty
      (reads_of_rulesTable fun _ declared => familyConsts_declared declared)
      ZFSetUniverseLift.carrierEmpty.2) t

/-- **Strong normalization of the package with the eleven laws on rule constants**: every term
typed in a formed context is strongly normalizing. -/
theorem ruleLaws_sn {n : Nat} {Θ : CCtx (Head L) n} {t T : CTm (Head L) n}
    (formed : CCtxFormed (ruleLaws L) Θ) (typing : CTyped (ruleLaws L) Θ t T) :
    StrongNormalization.SN
      (Rules.sum (rules L)
        (familyRules (rules L) (tableLookup (rulesTable L (proofTable L lawRows))) []))
      t.erase :=
  withRules_sn formed typing

/-- Each of the eleven laws has a proof in the package with the laws on rule constants: its
proof constant. -/
theorem ruleLaw_hasProof {φ : ClosedFormula UniverseSymbol} (law : φ ∈ universeTheory) :
    HasProof (ruleLaws L) constName φ := by
  have member : φ ∈ lawRows.map Prod.snd := lawRows_statements ▸ law
  obtain ⟨row, among, rfl⟩ := List.mem_map.mp member
  exact ⟨_, ruleLaws_typed row among⟩

/-- Each of the eleven laws with its connectives written out has a proof in the package with
the laws on rule constants. -/
theorem ruleExpandedLaw_hasProof {φ : ClosedFormula UniverseSymbol}
    (law : φ ∈ universeTheory.map expandInline) : HasProof (ruleLaws L) constName φ := by
  obtain ⟨source, among, rfl⟩ := List.mem_map.mp law
  exact (hasProof_expandInline ruleLaws_over.sets constName
    (constName_typed ruleLaws_over.sets)).mpr (ruleLaw_hasProof among)

/-- **A proof from the laws is a closed term of the package with the laws on rule
constants**, through the presentation by the rule constants. -/
theorem ruleLawProof_exists {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (ruleLaws L) constName equations)
    {Δ : List (ClosedFormula UniverseSymbol)} {φ : ClosedFormula UniverseSymbol}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline)
    (proof : ProofSyntaxModulo equations Δ φ) :
    ∃ t : CTm (Head L) 0, CTyped (ruleLaws L) .nil t (cHolds (trTerm φ)) :=
  hasProof_of_proof ruleLaws_over.sets (ruleOps_lawful ruleLaws_over) constName
    (constName_typed ruleLaws_over.sets) hold
    (fun δ member => (among δ member).elim ruleLaw_hasProof ruleExpandedLaw_hasProof) proof

/-- The proof constant of a law has the type of the proofs of the law in the package with the
laws on rule constants. -/
theorem ruleLawConstants_typed (i : Fin universeTheory.length) :
    CTyped (ruleLaws L) .nil (lawConstants i) (cHolds (trTerm (universeTheory.get i))) := by
  have typed := ruleLaws_typed (L := L) (lawRows.get (i.cast lawRows_length)) (List.get_mem _ _)
  have same : (lawRows.get (i.cast lawRows_length)).2 = universeTheory.get i := by
    rw [List.get_of_eq lawRows_statements.symm i, List.get_eq_getElem, List.get_eq_getElem,
      List.getElem_map]
    rfl
  rw [same] at typed
  exact typed

/-- **The term of a proof from the eleven laws by the rule constants**: each hypothesis is
discharged by the proof constant of its law. -/
theorem ruleLawProof_typed {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (ruleLaws L) constName equations) {φ : ClosedFormula UniverseSymbol}
    (proof : ProofSyntaxModulo equations universeTheory φ) :
    CTyped (ruleLaws L) .nil (trProof ruleOps constName proof idRen lawConstants)
      (cHolds (trTerm φ)) :=
  trProof_closed_typed ruleLaws_over.sets (ruleOps_lawful ruleLaws_over) constName
    (constName_typed ruleLaws_over.sets) hold proof ruleLawConstants_typed

include small large in
/-- **What has a proof in the package with the laws on rule constants is true in the model of
the logic**, relative to cofinally many inaccessible cardinals in two universes. -/
theorem models_of_ruleHasProof {φ : ClosedFormula UniverseSymbol}
    (proved : HasProof (ruleLaws L) constName φ) : (universeModel small).models φ := by
  obtain ⟨t, typed⟩ := proved
  by_contra false
  exact CDerivable.no_closed_inhabitant
    (ruleLaws_setModel small large (fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅))
    (notMem_holds_trTerm small large
      (reads_of_rulesTable fun _ declared => familyConsts_declared declared) false) t typed

include small large in
/-- **What the logic proves from the eleven laws, through the rule constants, is true in the
model of the logic.** -/
theorem ruleLawProof_sound {equations : List (HOL.DefiningEquation UniverseSymbol)}
    (hold : EquationsHold (ruleLaws L) constName equations)
    {Δ : List (ClosedFormula UniverseSymbol)} {φ : ClosedFormula UniverseSymbol}
    (among : ∀ δ ∈ Δ, δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline)
    (proof : ProofSyntaxModulo equations Δ φ) : (universeModel small).models φ :=
  models_of_ruleHasProof small large (ruleLawProof_exists hold among proof)

end RuleLaws

/-! ## Examples on the rule constants -/

section RuleExamples

/-! ### The empty set is a subset of every set -/

/-- **The term of the proof that the empty set is a subset of every set, by the rule
constants**:
`allI set (λ x. all set (λ y. imp (In y Empty) (In y x))) (λ x.`
`allI set (λ y. imp (In y Empty) (In y x)) (λ y.`
`impI (In y Empty) (In y x) (λ h. allE prop (λ r. r)`
`(impE (In y Empty) falsity (allE set (λ x. imp (In x Empty) falsity) emptyLaw y) h)`
`(In y x))))`. -/
def emptySubsetRuleTerm : CTm (Head L) 0 :=
  cAllI allSets (.lam allSets (cAll allSets (.lam allSets
      (cImp (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1))))))
    (.lam allSets (cAllI allSets (.lam allSets (cImp (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1))))
      (.lam allSets (cImpI (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1))
        (.lam (cHolds (cIn (.var 0) cEmpty))
          (cAllE cProp (.lam cProp (.var 0))
            (cImpE (cIn (.var 1) cEmpty) cFalse
              (cAllE allSets (.lam allSets (cImp (cIn (.var 0) cEmpty) cFalse)) (.const emptyLawN)
                (.var 1))
              (.var 0))
            (cIn (.var 1) (.var 2))))))))

omit [LevelOrder L] in
/-- The term of the proof by the rule constants, with the proof constant of the law for its
hypothesis, is that term. -/
theorem trProof_ruleOps_emptySubsetProof :
    trProof ruleOps constName emptySubsetProof idRen (fun _ => .const emptyLawN) =
      (emptySubsetRuleTerm : CTm (Head L) 0) := rfl

/-- The proof constant of the law of the empty set has the type of the proofs of the law in
the package with the laws on rule constants. -/
theorem ruleEmptyLaw_typed :
    CTyped (ruleLaws L) .nil (.const emptyLawN) (cHolds (trTerm (embed emptyLaw))) :=
  ruleProofConstant_typed rfl

/-- Positive example: **the empty set is a subset of every set, as a closed term of the
package with the laws on rule constants**, of the type of the proofs of the statement. -/
theorem emptySubsetRule_typed :
    CTyped (ruleLaws L) .nil emptySubsetRuleTerm
      (cHolds (cAll allSets (.lam allSets (cAll allSets (.lam allSets
        (cImp (cIn (.var 0) cEmpty) (cIn (.var 0) (.var 1)))))))) :=
  trProof_closed_typed ruleLaws_over.sets (ruleOps_lawful ruleLaws_over) constName
    (constName_typed ruleLaws_over.sets) (equationsHold_nil constName) emptySubsetProof
    (hyps := fun _ => .const emptyLawN) fun i => match i with
      | ⟨0, _⟩ => ruleEmptyLaw_typed

/-! ### No set is a member of the empty set, at an actual set and at a universe -/

/-- **A proof that no set is a member of the empty set, from the law of the empty set**, by
the four rules: for a set `x` and a proof `h` that `x` is a member of the empty set, the law
at `x` and `h` give falsity. Its statement is the law with its negation written out:
`∀ x. x ∈ Empty → ∀ r. r`. -/
def noMemberProof :
    ProofSyntaxModulo ([] : List (HOL.DefiningEquation UniverseSymbol))
      [expandInline (embed emptyLaw)] (expandInline (embed emptyLaw)) :=
  .allI (σ := .base ()) (.impI (φ := inSet (.var .vz) (.const (.core .empty))) (ψ := falsity)
    (.impE (φ := inSet (.var .vz) (.const (.core .empty))) (ψ := falsity)
      (.allE (φ := .imp (inSet (.var .vz) (.const (.core .empty))) falsity) (.var .vz)
        (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
          weakenHyps [expandInline (embed emptyLaw)]) ⟨1, by decide⟩))
      (.hyp (Δ := inSet (.var .vz) (.const (.core .empty)) ::
        weakenHyps [expandInline (embed emptyLaw)]) ⟨0, by decide⟩)))

/-- The predicate `λ (x : set). ¬ (x ∈ Empty)`, with its negation written out. -/
abbrev noMemberPredicate {n : Nat} : CTm (Head L) n :=
  .lam allSets (cImp (cIn (.var 0) cEmpty) cFalse)

/-- **The term of that proof**:
`allI set (λ x. ¬ (x ∈ Empty)) (λ x. impI (In x Empty) falsity (λ h.`
`impE (In x Empty) falsity (allE set (λ x. ¬ (x ∈ Empty)) emptyLaw x) h))`. -/
abbrev noMemberTerm {n : Nat} : CTm (Head L) n :=
  cAllI allSets noMemberPredicate
    (.lam allSets (cImpI (cIn (.var 0) cEmpty) cFalse (.lam (cHolds (cIn (.var 0) cEmpty))
      (cImpE (cIn (.var 1) cEmpty) cFalse
        (cAllE allSets noMemberPredicate (.const emptyLawN) (.var 1)) (.var 0)))))

omit [LevelOrder L] in
/-- The term of the proof by the rule constants is that term. -/
theorem trProof_noMemberProof :
    trProof ruleOps constName noMemberProof idRen (fun _ => .const emptyLawN) =
      (noMemberTerm : CTm (Head L) 0) := rfl

/-- **The proof that no set is a member of the empty set is a closed term of the package with
the laws on rule constants**, of the type of the proofs of `∀ x : set. ¬ (x ∈ Empty)`. -/
theorem noMemberTerm_typed :
    CTyped (ruleLaws L) .nil noMemberTerm (cHolds (cAll allSets noMemberPredicate)) :=
  trProof_closed_typed ruleLaws_over.sets (ruleOps_lawful ruleLaws_over) constName
    (constName_typed ruleLaws_over.sets) (equationsHold_nil constName) noMemberProof
    (hyps := fun _ => .const emptyLawN) fun i => match i with
      | ⟨0, _⟩ => ruleEmptyLaw_typed

/-- The proof that no set is a member of the empty set, at a set `s`: `allE set (λ x. ¬ (x ∈
Empty)) noMember s`. -/
abbrev noMemberAt (s : CTm (Head L) 0) : CTm (Head L) 0 :=
  cAllE allSets noMemberPredicate noMemberTerm s

/-- **Used by `allE` at a set, the proof proves that the set is not a member of the empty
set.** -/
theorem noMemberAt_typed {s : CTm (Head L) 0} (hs : CTyped (ruleLaws L) .nil s allSets) :
    CTyped (ruleLaws L) .nil (noMemberAt s) (cHolds (cImp (cIn s cEmpty) cFalse)) :=
  (ruleOps_lawful ruleLaws_over).allE (sets_typed ruleLaws_over.sets.contains)
    (cImp_typed ruleLaws_over.sets
      (cIn_typed ruleLaws_over.sets (.var 0) (empty_typed ruleLaws_over.sets))
      (cFalse_typed ruleLaws_over.sets))
    noMemberTerm_typed hs

/-- Positive example: **`Power Empty` is not a member of the empty set**, by the proof about
all sets at an actual set. -/
theorem noMemberAt_powerEmpty :
    CTyped (ruleLaws L) .nil (noMemberAt (cPower cEmpty))
      (cHolds (cImp (cIn (cPower cEmpty) cEmpty) cFalse)) :=
  noMemberAt_typed (powerEmpty_typed ruleLaws_over.sets)

/-- Positive example: **the universe at a level, read as a set, is not a member of the empty
set**, by the same proof at a carrier with a level. -/
theorem noMemberAt_universe (d : L) :
    CTyped (ruleLaws L) .nil (noMemberAt (universeAt d))
      (cHolds (cImp (cIn (universeAt d) cEmpty) cFalse)) :=
  noMemberAt_typed (universe_isSet ruleLaws_over.sets.contains d)

/-- The proof about all sets as a function on the sets, applied to a set:
`(λ (x : set). allE set (λ x. ¬ (x ∈ Empty)) noMember x) s`. -/
abbrev noMemberApplied (s : CTm (Head L) 0) : CTm (Head L) 0 :=
  .app (.lam allSets (cAllE allSets noMemberPredicate noMemberTerm (.var 0))) s

/-- **A step of the applied proof keeps its type.** The function on the sets, applied to a
set, is typed at the type of the proofs that the set is not a member of the empty set; it
takes a β-step to the proof used by `allE` at the set; and the reduct has the same type, by
the theorem on declared constants with no equation (`constants_reduces_typed`), not by
typing it again. -/
theorem noMemberApplied_step {s : CTm (Head L) 0} (hs : CTyped (ruleLaws L) .nil s allSets) :
    CTyped (ruleLaws L) .nil (noMemberApplied s) (cHolds (cImp (cIn s cEmpty) cFalse)) ∧
      CReduces (ruleLaws L) (noMemberApplied s) (noMemberAt s) ∧
      CTyped (ruleLaws L) .nil (noMemberAt s) (cHolds (cImp (cIn s cEmpty) cFalse)) := by
  have body : CTyped (ruleLaws L) (.snoc .nil allSets)
      (cAllE allSets noMemberPredicate noMemberTerm (.var 0))
      (cHolds (cImp (cIn (.var 0) cEmpty) cFalse)) :=
    (ruleOps_lawful ruleLaws_over).allE (sets_typed ruleLaws_over.sets.contains)
      (cImp_typed ruleLaws_over.sets
        (cIn_typed ruleLaws_over.sets (.var 0) (empty_typed ruleLaws_over.sets))
        (cFalse_typed ruleLaws_over.sets))
      (by
        have closed := (noMemberTerm_typed (L := L)).weaken (E := allSets)
        exact closed)
      (.var 0)
  have function : CTyped (ruleLaws L) .nil
      (.lam allSets (cAllE allSets noMemberPredicate noMemberTerm (.var 0)))
      (.pi allSets (cHolds (cImp (cIn (.var 0) cEmpty) cFalse))) :=
    .lamIntro (sets_typed ruleLaws_over.sets.contains)
      (ruleLaws_over.sets.contains.isUniverse (.sort _))
      (classToSet_typed ruleLaws_over.sets.contains (sets_typed ruleLaws_over.sets.contains)
        (cHolds_isSet ruleLaws_over.sets
          (cImp_typed ruleLaws_over.sets
            (cIn_typed ruleLaws_over.sets (.var 0) (empty_typed ruleLaws_over.sets))
            (cFalse_typed ruleLaws_over.sets))))
      (ruleLaws_over.sets.contains.isUniverse (.sort _)) body
  have applied : CTyped (ruleLaws L) .nil (noMemberApplied s)
      (cHolds (cImp (cIn s cEmpty) cFalse)) :=
    .appElim (B := cHolds (cImp (cIn (.var 0) cEmpty) cFalse)) function hs
  have step : CReduces (ruleLaws L) (noMemberApplied s) (noMemberAt s) :=
    .single (.betaPi allSets (cAllE allSets noMemberPredicate noMemberTerm (.var 0)) s)
  exact ⟨applied, step, constants_reduces_typed .nil step applied⟩

/-- Positive example: the step of the applied proof at `Power Empty` keeps its type. -/
theorem noMemberApplied_powerEmpty_step :
    CReduces (ruleLaws L) (noMemberApplied (cPower cEmpty)) (noMemberAt (cPower cEmpty)) ∧
      CTyped (ruleLaws L) .nil (noMemberAt (cPower cEmpty))
        (cHolds (cImp (cIn (cPower cEmpty) cEmpty) cFalse)) :=
  let result := noMemberApplied_step (powerEmpty_typed (ruleLaws_over (L := L)).sets)
  ⟨result.2.1, result.2.2⟩

/-- Positive example: **the proof that no set is a member of the empty set, as a function on
the sets applied to `Power Empty`, is strongly normalizing.** -/
theorem noMemberApplied_powerEmpty_sn :
    StrongNormalization.SN
      (Rules.sum (rules L)
        (familyRules (rules L) (tableLookup (rulesTable L (proofTable L lawRows))) []))
      (noMemberApplied (L := L) (cPower cEmpty)).erase :=
  ruleLaws_sn .nil (noMemberApplied_step (powerEmpty_typed (ruleLaws_over (L := L)).sets)).1

/-- Positive example: the step of the applied proof at the universe at a level, read as a
set, keeps its type. -/
theorem noMemberApplied_universe_step (d : L) :
    CReduces (ruleLaws L) (noMemberApplied (universeAt d)) (noMemberAt (universeAt d)) ∧
      CTyped (ruleLaws L) .nil (noMemberAt (universeAt d))
        (cHolds (cImp (cIn (universeAt d) cEmpty) cFalse)) :=
  let result := noMemberApplied_step (universe_isSet (ruleLaws_over (L := L)).sets.contains d)
  ⟨result.2.1, result.2.2⟩

/-! ### The two presentations where both apply -/

variable (L) in
/-- **The set theory with its equations, the eleven laws and the rule constants.** -/
abbrev lawsWithRules := withFamily (setLaws L) (ruleDecls L) []

omit [LevelOrder L] in
/-- The names of the rule constants are new to the proofs of the laws. -/
theorem ruleDecls_new_laws {c : DeclName} {T : CTm (Head L) 0}
    (declared : ruleDecls L c = some T) : proofDecls L lawRows c = none := by
  have row := tableLookup_mem declared
  simp only [ruleTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The package with the equations, the laws and the rule constants declares the rule
constants, over the set theory. -/
theorem lawsWithRules_over : OverSetTheoryRules (lawsWithRules L) where
  sets := OverSetTheory.of_sub
    ((ChurchRulesSub.sum_left _ _).trans (ChurchRulesSub.sum_left _ _))
  declared := fun declared => (withFamily_declared (setLaws L)
    ((withFamily_declared (setTheory L) ((setTheory_constantType _).trans
      (ruleDecls_new declared))).trans (ruleDecls_new_laws declared))).trans declared

/-- The package with the equations, the laws and the rule constants contains the steps of the
equations of the set theory. -/
theorem lawsWithRules_computes :
    StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) (lawsWithRules L) :=
  (withProofs_computes lawRows).trans (StepsWithin.sum_left _ _)

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {Const : Ty Unit → Type}
  (name : {A : Ty Unit} → Const A → DeclName)

/-- **The two presentations agree where both apply.** In a package with the equations of the
set theory and the rule constants, the term of a proof by the equations and its term by the
rule constants have the same type: the type of the proofs of the placed term of its
conclusion. -/
theorem presentations_agree (covers : OverSetTheoryRules Q)
    (computes : StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q)
    (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
      CTyped Q Γ (.const (name c)) (tyTm A))
    {equations : List (HOL.DefiningEquation Const)} (hold : EquationsHold Q name equations)
    {Γ : Ctx Unit} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo equations Δ φ) {m : Nat} {Θ : CCtx (Head L) m}
    {ρ : Ren Γ.length m} (placed : CCtxRen (ctxTm Γ) Θ ρ) {hyps : Fin Δ.length → CTm (Head L) m}
    (proved : ∀ i, CTyped Q Θ (hyps i) (cHolds ((trWith name (Δ.get i)).rename ρ))) :
    CTyped Q Θ (trProof equationOps name proof ρ hyps) (cHolds ((trWith name φ).rename ρ)) ∧
      CTyped Q Θ (trProof ruleOps name proof ρ hyps) (cHolds ((trWith name φ).rename ρ)) :=
  ⟨trProof_typed covers.sets (equationOps_lawful covers.sets computes) name named hold proof
      placed proved,
    trProof_typed covers.sets (ruleOps_lawful covers) name named hold proof placed proved⟩

/-- Positive example: **in the package with the equations, the laws and the rule constants, the
two terms of the proof that the empty set is a subset of every set have the same type.** -/
theorem emptySubset_presentations_agree :
    CTyped (lawsWithRules L) .nil emptySubsetTerm (cHolds (trTerm emptySubset)) ∧
      CTyped (lawsWithRules L) .nil emptySubsetRuleTerm (cHolds (trTerm emptySubset)) := by
  have law : CTyped (lawsWithRules L) .nil (.const emptyLawN)
      (cHolds (trTerm (expandInline (embed emptyLaw)))) :=
    CDerivable.mono (ChurchRulesSub.sum_left _ _) emptyLaw_typed
  have both := presentations_agree constName lawsWithRules_over lawsWithRules_computes
    (constName_typed lawsWithRules_over.sets) (equationsHold_nil constName) emptySubsetProof
    (Θ := .nil) (ρ := idRen) (fun i => i.elim0) (hyps := fun _ => .const emptyLawN)
    fun i => match i with
      | ⟨0, _⟩ => by rw [CTm.rename_id]; exact law
  rw [CTm.rename_id] at both
  exact ⟨both.1, both.2⟩

omit [LevelOrder L] in
/-- Negative example: **the two terms differ**: the presentations agree on types, not on
terms. -/
theorem emptySubsetTerm_ne_ruleTerm :
    (emptySubsetTerm : CTm (Head L) 0) ≠ emptySubsetRuleTerm := by
  intro same
  cases same

end RuleExamples

/-! ## Examples: retyping, defining equations, and the existential quantifier -/

section Examples

/-- A defining equation: the predicate `λ x. x ∈ Empty` at a set `y` is the statement
`y ∈ Empty`. -/
def memberEmptyAt : HOL.DefiningEquation UniverseSymbol where
  context := [.base ()]
  type := .prop
  left := .app (.lam (inSet (.var .vz) (.const (.core .empty)))) (.var .vz)
  right := inSet (.var .vz) (.const (.core .empty))

/-- Positive example: **a defining equation whose two sides are convertible by β holds in
every package over the set theory.** -/
theorem memberEmptyAt_holds {R' : Rules (Head L)} {Q : ChurchRules R'}
    (covers : OverSetTheory Q) : EquationsHold Q constName [memberEmptyAt] := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact trWith_betaConversion covers constName (constName_typed covers)
    (Relation.EqvGen.rel _ _ ⟨rfl, rfl,
      SourceStep.beta (inSet (.var .vz) (.const (.core .empty))) (.var .vz)⟩)

/-- The closed statement that the predicate `λ x. x ∈ Power x` holds at the empty set. -/
def powerPredicateAtEmpty : ClosedFormula UniverseSymbol :=
  .app (.lam (inSet (.var .vz) (.app (.const (.core .power)) (.var .vz))))
    (.const (.core .empty))

/-- The closed statement that the empty set is a member of its power set. -/
def emptyInPower : ClosedFormula UniverseSymbol :=
  inSet (.const (.core .empty)) (.app (.const (.core .power)) (.const (.core .empty)))

/-- A proof with a retyping: from the hypothesis that the predicate `λ x. x ∈ Power x` holds at
the empty set, the statement that the empty set is a member of its power set, by β. -/
def powerRetyping :
    ProofSyntaxModulo ([] : List (HOL.DefiningEquation UniverseSymbol))
      [powerPredicateAtEmpty] emptyInPower :=
  .convert
    (Relation.EqvGen.rel _ _ ⟨rfl, rfl,
      SourceStep.beta (inSet (.var .vz) (.app (.const (.core .power)) (.var .vz)))
        (.const (.core .empty))⟩)
    (.hyp ⟨0, by decide⟩)

omit [LevelOrder L] in
/-- Positive example: **a retyping leaves the term as it is**, in every presentation of the
proofs: the term of that proof is the term given for its hypothesis. -/
theorem trProof_powerRetyping (ops : ProofOps L) (h : CTm (Head L) 0) :
    trProof ops constName powerRetyping idRen (fun _ => h) = h := rfl

/-- So a proof that the predicate `λ x. x ∈ Power x` holds at the empty set is a proof that
the empty set is a member of its power set. -/
theorem powerRetyping_typed {R' : Rules (Head L)} {Q : ChurchRules R'}
    (covers : OverSetTheory Q)
    (computes : StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q)
    {h : CTm (Head L) 0}
    (proved : CTyped Q .nil h
      (cHolds (.app (.lam allSets (cIn (.var 0) (cPower (.var 0)))) cEmpty))) :
    CTyped Q .nil h (cHolds (cIn cEmpty (cPower cEmpty))) :=
  trProof_closed_typed covers (equationOps_lawful covers computes) constName
    (constName_typed covers) (equationsHold_nil constName) powerRetyping (hyps := fun _ => h)
    fun i => match i with
      | ⟨0, _⟩ => proved

/-- A defining equation that makes the statement that the empty set is a member of itself the
true statement. -/
def emptyInEmptyTrue : HOL.DefiningEquation UniverseSymbol where
  context := []
  type := .prop
  left := emptyInEmpty
  right := truth

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large in
/-- Negative example: **a defining equation of the logic need not hold in the package.** The
equation that makes `Empty ∈ Empty` the true statement does not hold in the package with the
laws: the true statement has a proof there, and `Empty ∈ Empty` has none. -/
theorem emptyInEmptyTrue_not_hold :
    ¬ EquationsHold (setLaws L) constName [emptyInEmptyTrue] := by
  intro hold
  have equal := hold emptyInEmptyTrue List.mem_cons_self
  obtain ⟨t, typed⟩ := hasProof_of_proof (Q := setLaws L) (withProofs_over lawRows)
    setLaws_equationOps_lawful constName (constName_typed (withProofs_over lawRows))
    (equationsHold_nil constName) (Δ := []) (φ := truth) (fun _ member => nomatch member)
    truthIntro
  exact emptyInEmpty_no_hasProof small large
    ⟨t, .conv typed (.symm (cHolds_congr (withProofs_over (L := L) lawRows) equal))
      ((withProofs_over (L := L) lawRows).contains.isUniverse (.sort _))⟩

/-- The closed statement that the empty set has a member: `∃ x. x ∈ Empty`. -/
def emptyHasMember : ClosedFormula UniverseSymbol :=
  .ex (inSet (.var .vz) (.const (.core .empty)))

omit [LevelOrder L] in
/-- Negative example: **the term of an existential statement and the term of the same
statement written out are different terms**; they are equal propositions
(`trWith_expandInline`). -/
theorem trTerm_ex_ne :
    (trTerm emptyHasMember : CTm (Head L) 0) ≠ trTerm (expandInline emptyHasMember) := by
  intro same
  cases same

end Examples

/-! ## The power set of a set lies in its universe

Three faces of one statement, `∀ N. Power N ∈ UnivOf N`.

* **Sets.** The statement is true in the model of the logic (`powerInUniverse_sound`), and that
  truth is the membership `powerInUniverse_true` records (`powerInUniverse_agrees`). The
  converse, `∀ N. UnivOf N ∈ Power N`, is false there (`universeInPower_false`).
* **Proof.** One proof in the checker's calculus is a closed term by the equations and a closed
  term by the rule constants, both of the type of the proofs of the statement, and the two
  terms differ. At `Empty` and at a universe read as a set, the proof gives the instance.
* **Nothing to run.** The term by the rule constants is strongly normalizing. The type of the
  proofs of the statement takes no step in the set theory on rule constants, and one declared
  step in the set theory with equations: the unfolding of the proofs of a quantification.
-/

section PowerInUniverse

open ZFSetUniverseClosure (univOf mem_univOf)
open ZFSetUniverseInterpretation (universeOf universeIn universeClosed closureFormula)
open Mettapedia.Logic.HOL.ImpredicativeConnectives

/-- **For every set `N`, the power set of `N` is a member of the universe around `N`.** -/
def powerInUniverseFormula : ClosedFormula UniverseSymbol :=
  .all (inSet (.app (.const (.core .power)) (.var .vz)) (universeOf (.var .vz)))

/-- **The converse: for every set `N`, the universe around `N` is a member of the power set
of `N`.** -/
def universeInPower : ClosedFormula UniverseSymbol :=
  .all (inSet (universeOf (.var .vz)) (.app (.const (.core .power)) (.var .vz)))

omit [LevelOrder L] in
/-- The term of the statement is the proposition `powerInUniverse` of the set theory. -/
theorem trTerm_powerInUniverseFormula :
    (trTerm powerInUniverseFormula : CTm (Head L) 0) = powerInUniverse := rfl

omit [LevelOrder L] in
/-- The term of the converse: `all set (λ N. In (UnivOf N) (Power N))`. -/
theorem trTerm_universeInPower :
    (trTerm universeInPower : CTm (Head L) 0) =
      cAll allSets (.lam allSets (cIn (cUnivOf (.var 0)) (cPower (.var 0)))) := rfl

/-- The two universe laws the proof uses, the closure with its conjunction written out. -/
def powerInUniverseLaws : List (ClosedFormula UniverseSymbol) :=
  [universeIn, expandInline universeClosed]

/-- A set is a member of the eleven laws. -/
theorem universeIn_in_theory : universeIn ∈ universeTheory :=
  List.mem_append.mpr (Or.inr List.mem_cons_self)

/-- Closure of the universe is one of the eleven laws. -/
theorem universeClosed_in_theory : universeClosed ∈ universeTheory :=
  List.mem_append.mpr (Or.inr
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- The hypotheses of the proof are laws, the closure with its conjunction written out. -/
theorem powerInUniverse_fromLaws (δ : ClosedFormula UniverseSymbol)
    (member : δ ∈ powerInUniverseLaws) :
    δ ∈ universeTheory ∨ δ ∈ universeTheory.map expandInline := by
  simp only [powerInUniverseLaws, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl universeIn_in_theory
  · exact Or.inr (List.mem_map.mpr ⟨universeClosed, universeClosed_in_theory, rfl⟩)

omit [LevelOrder L] in
/-- Instantiating a formula weakened under one binder, at the new variable, returns it. -/
theorem instantiate_lifted_self {τ : Ty Unit} (φ : Term UniverseSymbol [.base ()] τ) :
    HOL.instantiate (.var .vz)
      (HOL.rename (Rename.lift (σ := .base ()) (Rename.weaken (σ := .base ()))) φ) = φ := by
  unfold HOL.instantiate
  rw [Mettapedia.Logic.HOL.subst_rename]
  refine Eq.trans (Mettapedia.Logic.HOL.subst_ext ?_ φ) (Mettapedia.Logic.HOL.subst_id φ)
  intro _ i
  cases i with
  | vz => rfl
  | vs _ => rfl

omit [LevelOrder L] in
/-- Instantiating the power-set clause of a universe at its set is membership of the power set. -/
theorem instantiate_powerClosed (U : Term UniverseSymbol [.base ()] (.base ())) :
    HOL.instantiate (.var .vz)
      (.imp (inSet (.var .vz) (HOL.weaken U))
        (inSet (.app (.const (.core .power)) (.var .vz)) (HOL.weaken U))) =
      .imp (inSet (.var .vz) U) (inSet (.app (.const (.core .power)) (.var .vz)) U) := by
  change Term.imp
      (inSet (HOL.instantiate (.var .vz) (.var .vz)) (HOL.instantiate (.var .vz) (HOL.weaken U)))
      (inSet (.app (.const (.core .power)) (HOL.instantiate (.var .vz) (.var .vz)))
        (HOL.instantiate (.var .vz) (HOL.weaken U))) = _
  rw [show HOL.instantiate (.var .vz) (HOL.weaken U) = U from
    Mettapedia.Logic.HOL.instantiate_weaken (.var .vz) U]
  unfold HOL.instantiate HOL.subst Subst.single
  rfl

/-- **The proof that the power set of every set lies in its universe**, from `N ∈ UnivOf N`
and the power-set conjunct of the closure of `UnivOf N`, with conjunction written out. -/
def powerInUniverseProof :
    ProofSyntaxModulo ([] : List (HOL.DefiningEquation UniverseSymbol))
      powerInUniverseLaws powerInUniverseFormula :=
  .allI (σ := .base ())
    (.impE
      (Modulo.cast (instantiate_powerClosed (universeOf (.var .vz)))
        (.allE (.var .vz)
          (Modulo.conjunctionLeft
            (Modulo.conjunctionRight
              (Modulo.cast
                (instantiate_lifted_self
                  (expandInline (closureFormula (universeOf (.var .vz)))))
                (.allE (.var .vz)
                  (.hyp (Δ := weakenHyps powerInUniverseLaws) ⟨1, by decide⟩)))))))
      (Modulo.cast
        (instantiate_lifted_self (inSet (.var .vz) (universeOf (.var .vz))))
        (.allE (.var .vz)
          (.hyp (Δ := weakenHyps powerInUniverseLaws) ⟨0, by decide⟩))))

/-- The proof constant of each hypothesis: `universeIn`, then the closure written out. -/
def powerInUniverseHypTerm (i : Fin powerInUniverseLaws.length) : CTm (Head L) 0 :=
  match i with
  | ⟨0, _⟩ => .const universeInN
  | ⟨1, _⟩ => .const universeClosedN

/-- **The term of the proof by the equations.** -/
def powerInUniverseTerm : CTm (Head L) 0 :=
  trProof equationOps constName powerInUniverseProof idRen powerInUniverseHypTerm

/-- **The term of the proof by the rule constants.** -/
def powerInUniverseRuleTerm : CTm (Head L) 0 :=
  trProof ruleOps constName powerInUniverseProof idRen powerInUniverseHypTerm

omit [LevelOrder L] in
/-- The term by the equations is the translation of the proof. -/
theorem trProof_powerInUniverse :
    trProof equationOps constName powerInUniverseProof idRen powerInUniverseHypTerm =
      (powerInUniverseTerm : CTm (Head L) 0) := rfl

omit [LevelOrder L] in
/-- The term by the rule constants is the translation of the proof. -/
theorem trProof_powerInUniverseRule :
    trProof ruleOps constName powerInUniverseProof idRen powerInUniverseHypTerm =
      (powerInUniverseRuleTerm : CTm (Head L) 0) := rfl

omit [LevelOrder L] in
/-- **The two terms differ.** -/
theorem powerInUniverseTerm_ne_ruleTerm :
    (powerInUniverseTerm : CTm (Head L) 0) ≠ powerInUniverseRuleTerm := by
  intro same
  let headFlag (t : CTm (Head L) 0) : Bool :=
    match t with
    | .lam _ _ => true
    | _ => false
  have heads := congrArg headFlag same
  have leftHead : headFlag powerInUniverseTerm = true := rfl
  have rightHead : headFlag powerInUniverseRuleTerm = false := rfl
  rw [leftHead, rightHead] at heads
  cases heads

/-- The proof constant of `N ∈ UnivOf N` in the package with the laws. -/
theorem universeInLaw_typed :
    CTyped (setLaws L) .nil (.const universeInN) (cHolds (trTerm universeIn)) :=
  proofConstant_typed rfl rfl

/-- The proof constant of the closure in the package with the laws. -/
theorem universeClosedLaw_typed :
    CTyped (setLaws L) .nil (.const universeClosedN) (cHolds (trTerm universeClosed)) :=
  proofConstant_typed rfl rfl

/-- The closure constant has the type of the proofs of the closure with conjunction written
out. -/
theorem universeClosedLaw_expanded_typed :
    CTyped (setLaws L) .nil (.const universeClosedN)
      (cHolds (trTerm (expandInline universeClosed))) :=
  .conv universeClosedLaw_typed
    (holds_expandInline (Γ := []) (withProofs_over (L := L) lawRows) constName
      (constName_typed (withProofs_over (L := L) lawRows)) universeClosed)
    ((withProofs_over (L := L) lawRows).contains.isUniverse (.sort _))

/-- Each hypothesis constant has the type of the proofs of its hypothesis. -/
theorem powerInUniverseHyp_typed :
    ∀ i, CTyped (setLaws L) .nil (powerInUniverseHypTerm i)
      (cHolds (trTerm (powerInUniverseLaws.get i)))
  | ⟨0, _⟩ => universeInLaw_typed
  | ⟨1, _⟩ => universeClosedLaw_expanded_typed

/-- **The power set of every set lies in its universe, as a closed term of the package with
the laws**, of the type of the proofs of the statement. -/
theorem powerInUniverseTerm_typed :
    CTyped (setLaws L) .nil powerInUniverseTerm (cHolds (trTerm powerInUniverseFormula)) :=
  trProof_closed_typed (withProofs_over lawRows) setLaws_equationOps_lawful constName
    (constName_typed (withProofs_over lawRows)) (equationsHold_nil constName)
    powerInUniverseProof powerInUniverseHyp_typed

/-- The proof constant of `N ∈ UnivOf N` in the package with the laws on rule constants. -/
theorem ruleUniverseInLaw_typed :
    CTyped (ruleLaws L) .nil (.const universeInN) (cHolds (trTerm universeIn)) :=
  ruleProofConstant_typed rfl

/-- The proof constant of the closure in the package with the laws on rule constants. -/
theorem ruleUniverseClosedLaw_typed :
    CTyped (ruleLaws L) .nil (.const universeClosedN) (cHolds (trTerm universeClosed)) :=
  ruleProofConstant_typed rfl

/-- The closure constant on rule constants has the type of the proofs of the closure with
conjunction written out. -/
theorem ruleUniverseClosedLaw_expanded_typed :
    CTyped (ruleLaws L) .nil (.const universeClosedN)
      (cHolds (trTerm (expandInline universeClosed))) :=
  .conv ruleUniverseClosedLaw_typed
    (holds_expandInline (Γ := []) ruleLaws_over.sets constName
      (constName_typed ruleLaws_over.sets) universeClosed)
    (ruleLaws_over.sets.contains.isUniverse (.sort _))

/-- Each hypothesis constant has the type of the proofs of its hypothesis on rule constants. -/
theorem powerInUniverseHyp_ruleTyped :
    ∀ i, CTyped (ruleLaws L) .nil (powerInUniverseHypTerm i)
      (cHolds (trTerm (powerInUniverseLaws.get i)))
  | ⟨0, _⟩ => ruleUniverseInLaw_typed
  | ⟨1, _⟩ => ruleUniverseClosedLaw_expanded_typed

/-- **The power set of every set lies in its universe, as a closed term of the package with
the laws on rule constants**, of the type of the proofs of the statement. -/
theorem powerInUniverseRule_typed :
    CTyped (ruleLaws L) .nil powerInUniverseRuleTerm
      (cHolds (trTerm powerInUniverseFormula)) :=
  trProof_closed_typed ruleLaws_over.sets (ruleOps_lawful ruleLaws_over) constName
    (constName_typed ruleLaws_over.sets) (equationsHold_nil constName) powerInUniverseProof
    powerInUniverseHyp_ruleTyped

/-- The predicate `λ (N : set). Power N ∈ UnivOf N`. -/
abbrev powerInUniversePredicate {n : Nat} : CTm (Head L) n :=
  .lam allSets (cIn (cPower (.var 0)) (cUnivOf (.var 0)))

/-- The proof at a set `s`: `allE set (λ N. Power N ∈ UnivOf N) proof s`. -/
abbrev powerInUniverseAt (s : CTm (Head L) 0) : CTm (Head L) 0 :=
  cAllE allSets powerInUniversePredicate powerInUniverseRuleTerm s

/-- **Used by `allE` at a set, the proof proves that the power set of that set lies in its
universe.** -/
theorem powerInUniverseAt_typed {s : CTm (Head L) 0}
    (hs : CTyped (ruleLaws L) .nil s allSets) :
    CTyped (ruleLaws L) .nil (powerInUniverseAt s)
      (cHolds (cIn (cPower s) (cUnivOf s))) := by
  have ruleTyped : CTyped (ruleLaws L) .nil powerInUniverseRuleTerm
      (cHolds (cAll allSets powerInUniversePredicate)) := by
    have typed := powerInUniverseRule_typed (L := L)
    rwa [trTerm_powerInUniverseFormula] at typed
  exact (ruleOps_lawful ruleLaws_over).allE (sets_typed ruleLaws_over.sets.contains)
    (cIn_typed ruleLaws_over.sets
      (.appElim (B := allSets) (power_typed ruleLaws_over.sets) (.var 0))
      (.appElim (B := allSets) (univOf_typed ruleLaws_over.sets) (.var 0)))
    ruleTyped hs

/-- **`Power Empty` lies in `UnivOf Empty`**, by the proof about all sets at the empty set. -/
theorem powerInUniverseAt_empty :
    CTyped (ruleLaws L) .nil (powerInUniverseAt cEmpty)
      (cHolds (cIn (cPower cEmpty) (cUnivOf cEmpty))) :=
  powerInUniverseAt_typed (empty_typed ruleLaws_over.sets)

/-- **The power set of the universe at a level lies in the universe around it**, by the same
proof at a carrier with a level. -/
theorem powerInUniverseAt_universe (d : L) :
    CTyped (ruleLaws L) .nil (powerInUniverseAt (universeAt d))
      (cHolds (cIn (cPower (universeAt d)) (cUnivOf (universeAt d)))) :=
  powerInUniverseAt_typed (universe_isSet ruleLaws_over.sets.contains d)

/-- **What the proof concludes is true in the model of the logic**, through the rule
constants, relative to cofinally many inaccessible cardinals in two universes. -/
theorem powerInUniverse_sound (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) :
    (universeModel small).models powerInUniverseFormula :=
  ruleLawProof_sound (L := Nat) small large (equationsHold_nil constName) powerInUniverse_fromLaws
    powerInUniverseProof

/-- **What the proof concludes is true in the model of the logic**, through the package with
the laws and the equations. -/
theorem powerInUniverse_sound_equations (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) :
    (universeModel small).models powerInUniverseFormula :=
  lawProof_sound (L := Nat) small large (equationsHold_nil constName) powerInUniverse_fromLaws
    powerInUniverseProof

/-- **The proved statement is the statement `powerInUniverse_true` records**: in the set model,
the empty set lies in the type of the proofs of `powerInUniverse` exactly when the statement
is true in the model of the logic. -/
theorem powerInUniverse_agrees (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (ground : ZFSet.{u + 1}) (ν : Nat → Above L)
    {consts : DeclName → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (powerInUniverse (L := L))) Fin.elim0 ↔
      (universeModel small).models powerInUniverseFormula := by
  rw [← trTerm_powerInUniverseFormula]
  exact empty_mem_holds_trTerm_iff (L := L) small large reads powerInUniverseFormula

/-- **The set model sees the proved statement**: the empty set lies in the type of the proofs
of `powerInUniverse`. -/
theorem powerInUniverse_proved_true (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (ground : ZFSet.{u + 1}) (ν : Nat → Above L)
    {consts : DeclName → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (powerInUniverse (L := L))) Fin.elim0 :=
  (powerInUniverse_agrees small large ground ν reads).mpr (powerInUniverse_sound small large)

/-- **Nothing to run, on the proof term**: the term by the rule constants is strongly
normalizing. -/
theorem powerInUniverseRule_sn :
    StrongNormalization.SN
      (Rules.sum (rules L)
        (familyRules (rules L) (tableLookup (rulesTable L (proofTable L lawRows))) []))
      (powerInUniverseRuleTerm : CTm (Head L) 0).erase :=
  ruleLaws_sn .nil powerInUniverseRule_typed

/-- **Nothing to run, on the type of the proofs**: in the set theory on rule constants the
type of the proofs of the statement takes no step. -/
theorem powerInUniverse_noStep {r : CTm (Head L) 0} :
    ¬ (setTheoryRules L).computation.step (cHolds (powerInUniverse (L := L))) r :=
  constants_noSteps

/-- **One declared step**: in the set theory with equations, the type of the proofs of the
statement unfolds to a function type over all the sets. -/
theorem powerInUniverse_unfolds :
    (setTheory L).computation.step (cHolds (powerInUniverse (L := L)) : CTm (Head L) 0)
      (.pi allSets (cHolds (.app (powerInUniversePredicate.rename wk) (.var 0)))) :=
  .inr ⟨holdsAll L, List.mem_cons_of_mem _ List.mem_cons_self,
    ![powerInUniversePredicate, allSets], rfl, rfl⟩

/-- **The converse is false in the model of the logic**: the universe around the empty set is
not a member of the power set of the empty set. -/
theorem universeInPower_false (h : CofinalInaccessibles.{u}) :
    ¬ (universeModel h).models universeInPower := by
  intro holds
  have member : univOf h (∅ : ZFSet.{u}) ∈ ZFSet.powerset (∅ : ZFSet.{u}) :=
    holds (∅ : ZFSet.{u}) trivial
  exact ZFSet.notMem_empty _
    ((ZFSet.mem_powerset.mp member) (mem_univOf h (∅ : ZFSet.{u})))

/-- **No closed term of the package with the laws on rule constants proves the converse**,
relative to cofinally many inaccessible cardinals in two universes. -/
theorem universeInPower_no_term (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (t : CTm (Head L) 0) :
    ¬ CTyped (ruleLaws L) .nil t (cHolds (trTerm universeInPower)) :=
  fun typed => universeInPower_false small (models_of_ruleHasProof small large ⟨t, typed⟩)

end PowerInUniverse

/-! ## A pair keeps its set, and a proof of existence does not return the witness -/

section ExistenceAgainstAPair

open ZFSetTraceProducts (traceApp traceLam tracePiSet traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetDependentProducts (graph)
open Mettapedia.SetTheory.ZFSetOrderedPair (first first_pair)

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}

/-! ### A pair keeps its set -/

/-- The type of a set paired with a proof that `P` holds of it. It is a type of `allClasses`. -/
def witnessPairType (P : CTm (Head L) n) : CTm (Head L) n :=
  .sigma allSets (cHolds (.app (P.rename wk) (.var 0)))

omit [LevelOrder L] in
/-- Opening the family of proofs at a set is the proofs that `P` holds of the set. -/
theorem witnessFamily_inst (a P : CTm (Head L) n) :
    CTm.inst0 a (cHolds (.app (P.rename wk) (.var 0))) = cHolds (.app P a) := by
  show cHolds (.app (CTm.inst0 a (P.rename wk)) a) = _
  rw [CTm.inst0_rename_wk]

/-- **The pair type is a type of `allClasses`.** -/
theorem witnessPairType_typed (covers : OverSetTheory Q) {P : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) :
    CTyped Q Γ (witnessPairType P) allClasses := by
  have family : CTyped Q (.snoc Γ allSets) (cHolds (.app (P.rename wk) (.var 0))) allSets :=
    cHolds_isSet covers (.appElim (B := cProp) (hP.weaken (E := allSets)) (.var 0))
  exact CDerivable.cumul
    (.sigmaForm (sets_typed covers.contains) (covers.contains.isUniverse (.sort _)) family
      (covers.contains.isUniverse (.sort _)) (covers.contains.join (.sorts _ _)))
    (covers.contains.cumulative
      (u := .sort (.max (.const (.above 1)) (.const (.above 0))))
      (v := .sort (.const (.above 1)))
      fun _ => max_le (le_refl _) (Above.above_le_above.mpr (Nat.zero_le 1)))

/-- **A pair of a set and a proof that `P` holds of it has the pair type.** -/
theorem witnessPair_typed (covers : OverSetTheory Q) {P a p : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (ha : CTyped Q Γ a allSets)
    (hp : CTyped Q Γ p (cHolds (.app P a))) :
    CTyped Q Γ (.pair a p) (witnessPairType P) :=
  .pairIntro (witnessPairType_typed covers hP) (covers.contains.isUniverse (.sort _)) ha
    (by rw [witnessFamily_inst]; exact hp)

/-- **`fst` of the pair is a set.** -/
theorem witnessFst_typed (covers : OverSetTheory Q) {P a p : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (ha : CTyped Q Γ a allSets)
    (hp : CTyped Q Γ p (cHolds (.app P a))) :
    CTyped Q Γ (.fst (.pair a p)) allSets :=
  .fstElim (witnessPair_typed covers hP ha hp)

/-- **`fst` of the pair is the set it was built with.** -/
theorem witnessFst_equal (covers : OverSetTheory Q) {P a p : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (ha : CTyped Q Γ a allSets)
    (hp : CTyped Q Γ p (cHolds (.app P a))) :
    CEqual Q Γ (.fst (.pair a p)) a allSets :=
  .betaFst (witnessPairType_typed covers hP) (covers.contains.isUniverse (.sort _)) ha
    (by rw [witnessFamily_inst]; exact hp)

/-- **In the set model, `fst` of the pair has the value of the set**, for either package. -/
theorem witnessFst_value {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    {a p : CTm Head 0} :
    ev heads consts (.fst (.pair a p)) Fin.elim0 = ev heads consts a Fin.elim0 := by
  show first (ZFSet.pair (ev heads consts a Fin.elim0) (ev heads consts p Fin.elim0)) = _
  rw [first_pair]

/-! ### The proofs of an equality are the identity -/

variable (computes : StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q)

include computes

/-- **The proofs of an equality are the proofs of the identity**, in every package over the
set theory that contains the steps of its equations. -/
theorem holds_eq_rule (covers : OverSetTheory Q) {T a b : CTm (Head L) n}
    (hT : CTyped Q Γ T allClasses) (ha : CTyped Q Γ a T) (hb : CTyped Q Γ b T) :
    CEqual Q Γ (cHolds (cEq T a b)) (.id T a b) allClasses :=
  have typed : CSubstMor Q (holdsEq L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => b
        | ⟨1, _⟩ => a
        | ⟨2, _⟩ => T) :=
    fun j => match j with
      | ⟨0, _⟩ => hb
      | ⟨1, _⟩ => ha
      | ⟨2, _⟩ => hT
  family_equation_holds (rules L) computes
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ typed
    (set_isClass covers.contains (cHolds_isSet covers (cEq_typed covers hT ha hb)))
    (.idForm hT (covers.contains.isUniverse (.sort _)) ha hb)

/-- **Reflexivity proves an equality**, where the equations make the proofs of an equality
the proofs of the identity. -/
theorem eqRefl_typed (covers : OverSetTheory Q) {T a : CTm (Head L) n}
    (hT : CTyped Q Γ T allClasses) (ha : CTyped Q Γ a T) :
    CTyped Q Γ (.refl a) (cHolds (cEq T a a)) :=
  .conv (.reflIntro ha) (.symm (holds_eq_rule computes covers hT ha ha))
    (covers.contains.isUniverse (.sort _))

omit computes

/-- **`eqI T a b e` proves `eq T a b`** from a proof `e` of the identity. -/
theorem cEqI_typed (covers : OverSetTheoryRules Q) {T a b e : CTm (Head L) n}
    (hT : CTyped Q Γ T allClasses) (ha : CTyped Q Γ a T) (hb : CTyped Q Γ b T)
    (he : CTyped Q Γ e (.id T a b)) :
    CTyped Q Γ (cEqI T a b e) (cHolds (cEq T a b)) := by
  have first := CDerivable.appElim
      (B := .pi (.var 0) (.pi (.var 1)
        (.pi (.id (.var 2) (.var 1) (.var 0)) (cHolds (cEq (.var 3) (.var 2) (.var 1))))))
      (eqI_typed covers) hT
  have same : CTm.inst0 T (.pi (.var 0) (.pi (.var 1)
        (.pi (.id (.var 2) (.var 1) (.var 0)) (cHolds (cEq (.var 3) (.var 2) (.var 1)))))) =
      (.pi T (.pi (T.rename wk)
        (.pi (.id ((T.rename wk).rename wk) (.var 1) (.var 0))
          (cHolds (cEq (((T.rename wk).rename wk).rename wk) (.var 2) (.var 1))))) :
        CTm (Head L) n) := by
    show CTm.pi (CTm.inst0 T (.var 0))
        (.pi (CTm.subst (CTm.liftSub (CTm.subst0 T)) (.var 1))
          (.pi (.id (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 T))) (.var 2))
              (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 T))) (.var 1))
              (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 T))) (.var 0)))
            (cHolds (cEq
              (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.liftSub (CTm.subst0 T)))) (.var 3))
              (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.liftSub (CTm.subst0 T)))) (.var 2))
              (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.liftSub (CTm.subst0 T)))) (.var 1)))))) = _
    rfl
  rw [same] at first
  have second := CDerivable.appElim first ha
  have sameA : CTm.inst0 a (.pi (T.rename wk)
        (.pi (.id ((T.rename wk).rename wk) (.var 1) (.var 0))
          (cHolds (cEq (((T.rename wk).rename wk).rename wk) (.var 2) (.var 1))))) =
      (.pi T (.pi (.id (T.rename wk) (a.rename wk) (.var 0))
        (cHolds (cEq ((T.rename wk).rename wk) ((a.rename wk).rename wk) (.var 1)))) :
        CTm (Head L) n) := by
    show CTm.pi (CTm.inst0 a (T.rename wk))
        (.pi (.id (CTm.subst (CTm.liftSub (CTm.subst0 a)) ((T.rename wk).rename wk))
            (CTm.subst (CTm.liftSub (CTm.subst0 a)) (.var 1))
            (CTm.subst (CTm.liftSub (CTm.subst0 a)) (.var 0)))
          (cHolds (cEq
            (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 a)))
              (((T.rename wk).rename wk).rename wk))
            (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 a))) (.var 2))
            (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 a))) (.var 1))))) = _
    rw [CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk, CTm.subst_liftSub_wk,
      CTm.liftSub_subst0_rename_wk]
    rfl
  rw [sameA] at second
  have third := CDerivable.appElim second hb
  have sameB : CTm.inst0 b (.pi (.id (T.rename wk) (a.rename wk) (.var 0))
        (cHolds (cEq ((T.rename wk).rename wk) ((a.rename wk).rename wk) (.var 1)))) =
      (.pi (.id T a b) (cHolds (cEq (T.rename wk) (a.rename wk) (b.rename wk))) :
        CTm (Head L) n) := by
    show CTm.pi (.id (CTm.inst0 b (T.rename wk)) (CTm.inst0 b (a.rename wk))
          (CTm.inst0 b (.var 0)))
        (cHolds (cEq (CTm.subst (CTm.liftSub (CTm.subst0 b)) ((T.rename wk).rename wk))
          (CTm.subst (CTm.liftSub (CTm.subst0 b)) ((a.rename wk).rename wk))
          (CTm.subst (CTm.liftSub (CTm.subst0 b)) (.var 1)))) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk, CTm.liftSub_subst0_rename_wk,
      CTm.liftSub_subst0_rename_wk]
    rfl
  rw [sameB] at third
  have fourth := CDerivable.appElim third he
  rwa [show CTm.inst0 e (cHolds (cEq (T.rename wk) (a.rename wk) (b.rename wk))) =
      cHolds (cEq T a b) by
    show cHolds (cEq (CTm.inst0 e (T.rename wk)) (CTm.inst0 e (a.rename wk))
      (CTm.inst0 e (b.rename wk))) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk, CTm.inst0_rename_wk]] at fourth

/-- **`eqI` at reflexivity proves an equality.** -/
theorem eqIRefl_typed (covers : OverSetTheoryRules Q) {T a : CTm (Head L) n}
    (hT : CTyped Q Γ T allClasses) (ha : CTyped Q Γ a T) :
    CTyped Q Γ (cEqI T a a (.refl a)) (cHolds (cEq T a a)) :=
  cEqI_typed covers hT ha ha (.reflIntro ha)

/-! ### Existence, where the equations make the proofs functions -/

/-- The body of the witness quantifier inside an existential over the sets. -/
def exPredBody (P : CTm (Head L) n) : CTm (Head L) (n + 2) :=
  cImp (.app ((P.rename wk).rename wk) (.var 0)) (.var 1)

/-- The quantifier `all set (λ x. P x → r)` under the motive `r`. -/
def exWitnessAll (P : CTm (Head L) n) : CTm (Head L) (n + 1) :=
  cAll allSets (.lam allSets (exPredBody P))

/-- The motive of an existential over the sets: `(all set (λ x. P x → r)) → r`. -/
def exMotive (P : CTm (Head L) n) : CTm (Head L) (n + 1) :=
  cImp (exWitnessAll P) (.var 0)

/-- **Introduction of an existential**: `λ R k. k a p`. -/
def exIntro (P a p : CTm (Head L) n) : CTm (Head L) n :=
  .lam cProp (.lam (cHolds (exWitnessAll P))
    (.app (.app (.var 0) ((a.rename wk).rename wk)) ((p.rename wk).rename wk)))

/-- **Elimination of an existential**: the proof applied to the motive and to its proof. -/
def exElim (h R k : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app h R) k

/-- The instance of the witness quantifier at a proposition: `all set (λ x. P x → R)`. -/
def exElimPred (P R : CTm (Head L) n) : CTm (Head L) n :=
  cAll allSets (.lam allSets (cImp (.app (P.rename wk) (.var 0)) (R.rename wk)))

omit [LevelOrder L] in
/-- An existential over the sets is quantification of its motive. -/
theorem cEx_allSets_eq (P : CTm (Head L) n) :
    cEx allSets P = cAll cProp (.lam cProp (exMotive P)) := rfl

omit [LevelOrder L] in
/-- Opening the witness quantifier at a proposition is the quantifier into that proposition. -/
theorem inst0_exWitnessAll (R P : CTm (Head L) n) :
    CTm.inst0 R (exWitnessAll P) = exElimPred P R := by
  unfold exWitnessAll exPredBody exElimPred
  show cAll (CTm.inst0 R allSets) (.lam (CTm.inst0 R allSets)
      (cImp (.app (CTm.subst (CTm.liftSub (CTm.subst0 R)) ((P.rename wk).rename wk))
          (CTm.subst (CTm.liftSub (CTm.subst0 R)) (.var 0)))
        (CTm.subst (CTm.liftSub (CTm.subst0 R)) (.var 1)))) = _
  rw [CTm.liftSub_subst0_rename_wk]
  rfl

omit [LevelOrder L] in
/-- Opening the motive at a proposition is the implication into that proposition. -/
theorem inst0_exMotive (R P : CTm (Head L) n) :
    CTm.inst0 R (exMotive P) = cImp (exElimPred P R) R := by
  unfold exMotive
  show cImp (CTm.inst0 R (exWitnessAll P)) (CTm.inst0 R (.var 0)) = _
  rw [inst0_exWitnessAll]
  rfl

omit [LevelOrder L] in
/-- Applying the witness quantifier's proof to a set opens the implication. -/
theorem exIntro_app_type (a P : CTm (Head L) n) :
    CTm.inst0 ((a.rename wk).rename wk) (cHolds ((exPredBody P).rename (liftRen wk))) =
      cHolds (cImp (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) (.var 1)) := by
  unfold exPredBody
  show cHolds (cImp
      (.app (CTm.inst0 ((a.rename wk).rename wk)
          (CTm.rename (liftRen wk) ((P.rename wk).rename wk)))
        (CTm.inst0 ((a.rename wk).rename wk) (.var 0)))
      (CTm.inst0 ((a.rename wk).rename wk) (CTm.rename (liftRen wk) (.var 1)))) = _
  rw [CTm.rename_liftRen_wk, CTm.inst0_rename_wk]
  rfl

omit [LevelOrder L] in
/-- Applying the implication's proof opens the motive. -/
theorem exIntro_imp_type (p : CTm (Head L) (n + 2)) :
    CTm.inst0 p (cHolds (.var 2)) = cHolds (.var 1) := by
  show cHolds (CTm.inst0 p (.var 2)) = _
  rfl

omit [LevelOrder L] in
/-- Applying the existential to a proposition opens the implication into it. -/
theorem exElim_at_type (R P : CTm (Head L) n) :
    CTm.inst0 R (cHolds (exMotive P)) = cHolds (cImp (exElimPred P R) R) := by
  show cHolds (CTm.inst0 R (exMotive P)) = _
  rw [inst0_exMotive]

omit [LevelOrder L] in
/-- The conclusion of that implication, opened at its proof, is the proposition. -/
theorem exElim_done_type (k R : CTm (Head L) n) :
    CTm.inst0 k (cHolds (R.rename wk)) = cHolds R := by
  show cHolds (CTm.inst0 k (R.rename wk)) = _
  rw [CTm.inst0_rename_wk]

/-- **The witness quantifier of an existential over the sets is a proposition.** -/
theorem exWitnessAll_typed (covers : OverSetTheory Q) {P : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) :
    CTyped Q (.snoc Γ cProp) (exWitnessAll P) cProp := by
  have body : CTyped Q (.snoc (.snoc Γ cProp) allSets) (exPredBody P) cProp := by
    refine cImp_typed covers ?_ (.var 1)
    exact .appElim (B := cProp) ((hP.weaken (E := cProp)).weaken (E := allSets)) (.var 0)
  exact cAll_typed covers (sets_typed covers.contains)
    (.lamIntro (sets_typed covers.contains) (covers.contains.isUniverse (.sort _))
      (classToClass_typed covers.contains (sets_typed covers.contains) (prop_isClass covers))
      (covers.contains.isUniverse (.sort _)) body)

/-- **The motive of an existential over the sets is a proposition.** -/
theorem exMotive_typed (covers : OverSetTheory Q) {P : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) :
    CTyped Q (.snoc Γ cProp) (exMotive P) cProp :=
  cImp_typed covers (exWitnessAll_typed covers hP) (.var 0)

/-- **`all set (λ x. P x → R)` is a proposition.** -/
theorem exElimPred_typed (covers : OverSetTheory Q) {P R : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (hR : CTyped Q Γ R cProp) :
    CTyped Q Γ (exElimPred P R) cProp := by
  have body : CTyped Q (.snoc Γ allSets)
      (cImp (.app (P.rename wk) (.var 0)) (R.rename wk)) cProp :=
    cImp_typed covers (.appElim (B := cProp) (hP.weaken (E := allSets)) (.var 0))
      (hR.weaken (E := allSets))
  exact cAll_typed covers (sets_typed covers.contains)
    (.lamIntro (sets_typed covers.contains) (covers.contains.isUniverse (.sort _))
      (classToClass_typed covers.contains (sets_typed covers.contains) (prop_isClass covers))
      (covers.contains.isUniverse (.sort _)) body)

include computes

/-- **`λ R k. k a p` proves that `P` holds of some set**, where the equations make the proofs
of an implication and of a quantification the functions. -/
theorem exIntro_typed (covers : OverSetTheory Q) {P a p : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (ha : CTyped Q Γ a allSets)
    (hp : CTyped Q Γ p (cHolds (.app P a))) :
    CTyped Q Γ (exIntro P a p) (cHolds (cEx allSets P)) := by
  have witnessProp := exWitnessAll_typed covers hP
  have motiveProp := exMotive_typed covers hP
  let Γk := (Γ.snoc cProp).snoc (cHolds (exWitnessAll P))
  have body : CTyped Q (.snoc (.snoc Γ cProp) allSets) (exPredBody P) cProp := by
    refine cImp_typed covers ?_ (.var 1)
    exact .appElim (B := cProp) ((hP.weaken (E := cProp)).weaken (E := allSets)) (.var 0)
  have opened := (holds_all_lam_rule covers computes (sets_typed covers.contains) body).weaken
    (E := cHolds (exWitnessAll P))
  have kFun := CDerivable.conv (CDerivable.var (P := Q) (Γ := Γk) 0) opened
    (covers.contains.isUniverse (.sort _))
  have a2 : CTyped Q Γk ((a.rename wk).rename wk) allSets :=
    (ha.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))
  have applied : CTyped Q Γk (.app (.var 0) ((a.rename wk).rename wk))
      (cHolds (cImp (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) (.var 1))) := by
    rw [← exIntro_app_type]
    exact CDerivable.appElim kFun a2
  have prem : CTyped Q Γk (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) cProp :=
    .appElim (B := cProp)
      ((hP.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))) a2
  have goalR : CTyped Q Γk (.var 1) cProp := CDerivable.var (P := Q) (Γ := Γk) 1
  have asImpFun := CDerivable.conv applied (holds_imp_rule covers computes prem goalR)
    (covers.contains.isUniverse (.sort _))
  have p2 : CTyped Q Γk ((p.rename wk).rename wk)
      (cHolds (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk))) :=
    (hp.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))
  have eliminated : CTyped Q Γk
      (.app (.app (.var 0) ((a.rename wk).rename wk)) ((p.rename wk).rename wk))
      (cHolds (.var 1)) := by
    rw [← exIntro_imp_type]
    exact CDerivable.appElim asImpFun p2
  have domainK : CTyped Q (.snoc Γ cProp) (cHolds (exWitnessAll P)) U0 :=
    cHolds_typed covers witnessProp
  have innerTy := smallFunctions_typed covers.contains domainK
    (cHolds_typed covers goalR)
  have inner := CDerivable.lamIntro domainK (covers.contains.isUniverse (.sort _)) innerTy
    (covers.contains.isUniverse (.sort _)) eliminated
  have asImp := CDerivable.conv inner
    (.symm (holds_imp_rule covers computes witnessProp (CDerivable.var (P := Q) 0)))
    (covers.contains.isUniverse (.sort _))
  have outerTy := classToSet_typed covers.contains (prop_isClass covers)
    (cHolds_isSet covers motiveProp)
  have outer := CDerivable.lamIntro (prop_isClass covers) (covers.contains.isUniverse (.sort _))
    outerTy (covers.contains.isUniverse (.sort _)) asImp
  exact CDerivable.conv outer
    (.symm (holds_all_lam_rule covers computes (prop_isClass covers) motiveProp))
    (covers.contains.isUniverse (.sort _))

/-- **An existential eliminates into any proposition**: from a proof of the existential and a
proof that every witness yields the proposition. -/
theorem exElim_typed (covers : OverSetTheory Q) {P h R k : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (hR : CTyped Q Γ R cProp)
    (hh : CTyped Q Γ h (cHolds (cEx allSets P)))
    (hk : CTyped Q Γ k (cHolds (exElimPred P R))) :
    CTyped Q Γ (exElim h R k) (cHolds R) := by
  have motiveProp := exMotive_typed covers hP
  have asFun := CDerivable.conv hh
    (holds_all_lam_rule covers computes (prop_isClass covers) motiveProp)
    (covers.contains.isUniverse (.sort _))
  have atR : CTyped Q Γ (.app h R) (cHolds (cImp (exElimPred P R) R)) := by
    rw [← exElim_at_type]
    exact CDerivable.appElim asFun hR
  have predProp := exElimPred_typed covers hP hR
  have asImp := CDerivable.conv atR (holds_imp_rule covers computes predProp hR)
    (covers.contains.isUniverse (.sort _))
  have done : CTyped Q Γ (.app (.app h R) k) (cHolds R) := by
    rw [← exElim_done_type]
    exact CDerivable.appElim asImp hk
  exact done

omit computes

/-- The set theory contains the steps of its equations. -/
theorem setTheory_steps :
    StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) (setTheory L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (setDecls L) (setEquations L))

/-- **In the set theory, `λ R k. k a p` proves that `P` holds of some set.** -/
theorem setTheory_exIntro_typed {P a p : CTm (Head L) 0}
    (hP : CTyped (setTheory L) .nil P (.pi allSets cProp))
    (ha : CTyped (setTheory L) .nil a allSets)
    (hp : CTyped (setTheory L) .nil p (cHolds (.app P a))) :
    CTyped (setTheory L) .nil (exIntro P a p) (cHolds (cEx allSets P)) :=
  exIntro_typed setTheory_steps setTheory_over hP ha hp

/-- **In the set theory, an existential eliminates into any proposition.** -/
theorem setTheory_exElim_typed {P h R k : CTm (Head L) 0}
    (hP : CTyped (setTheory L) .nil P (.pi allSets cProp))
    (hR : CTyped (setTheory L) .nil R cProp)
    (hh : CTyped (setTheory L) .nil h (cHolds (cEx allSets P)))
    (hk : CTyped (setTheory L) .nil k (cHolds (exElimPred P R))) :
    CTyped (setTheory L) .nil (exElim h R k) (cHolds R) :=
  exElim_typed setTheory_steps setTheory_over hP hR hh hk

/-! ### Existence, by the rule constants -/

omit [LevelOrder L] in
/-- Opening the witness implication at a set is the implication into the motive. -/
theorem exIntro_beta_prop (a P : CTm (Head L) n) :
    CTm.inst0 ((a.rename wk).rename wk) ((exPredBody P).rename (liftRen wk)) =
      cImp (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) (.var 1) := by
  unfold exPredBody
  show cImp
      (.app (CTm.inst0 ((a.rename wk).rename wk)
          (CTm.rename (liftRen wk) ((P.rename wk).rename wk)))
        (CTm.inst0 ((a.rename wk).rename wk) (.var 0)))
      (CTm.inst0 ((a.rename wk).rename wk) (CTm.rename (liftRen wk) (.var 1))) = _
  rw [CTm.rename_liftRen_wk, CTm.inst0_rename_wk]
  rfl

/-- **Introduction of an existential by the rule constants**: `allI`, `impI`, `allE` and
`impE` in place of the two abstractions and the two applications. -/
def exIntroByRules (P a p : CTm (Head L) n) : CTm (Head L) n :=
  cAllI cProp (.lam cProp (exMotive P))
    (.lam cProp
      (cImpI (exWitnessAll P) (.var 0)
        (.lam (cHolds (exWitnessAll P))
          (cImpE
            (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk))
            (.var 1)
            (cAllE allSets ((CTm.lam allSets (exPredBody P)).rename wk) (.var 0)
              ((a.rename wk).rename wk))
            ((p.rename wk).rename wk)))))

/-- **Elimination of an existential by the rule constants.** -/
def exElimByRules (P h R k : CTm (Head L) n) : CTm (Head L) n :=
  cImpE (exElimPred P R) R (cAllE cProp (.lam cProp (exMotive P)) h R) k

/-- **`allE` at the motive, then `impE`, proves the proposition**, in every package that
declares the rule constants. -/
theorem exElimByRules_typed (covers : OverSetTheoryRules Q) {P h R k : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (hR : CTyped Q Γ R cProp)
    (hh : CTyped Q Γ h (cHolds (cEx allSets P)))
    (hk : CTyped Q Γ k (cHolds (exElimPred P R))) :
    CTyped Q Γ (exElimByRules P h R k) (cHolds R) := by
  have motive := exMotive_typed covers.sets hP
  have pred : CTyped Q Γ (.lam cProp (exMotive P)) (.pi cProp cProp) :=
    .lamIntro (prop_isClass covers.sets) (covers.sets.contains.isUniverse (.sort _))
      (classToClass_typed covers.sets.contains (prop_isClass covers.sets)
        (prop_isClass covers.sets))
      (covers.sets.contains.isUniverse (.sort _)) motive
  have atApp := cAllE_typed covers (prop_isClass covers.sets) pred hh hR
  have beta : CEqual Q Γ (.app (.lam cProp (exMotive P)) R) (CTm.inst0 R (exMotive P)) cProp :=
    .betaPi (B := cProp)
      (classToClass_typed covers.sets.contains (prop_isClass covers.sets)
        (prop_isClass covers.sets))
      (covers.sets.contains.isUniverse (.sort _)) motive hR
  have opened : CTyped Q Γ (cAllE cProp (.lam cProp (exMotive P)) h R)
      (cHolds (cImp (exElimPred P R) R)) := by
    rw [← inst0_exMotive]
    exact CDerivable.conv atApp (cHolds_congr covers.sets beta)
      (covers.sets.contains.isUniverse (.sort _))
  exact cImpE_typed covers (exElimPred_typed covers.sets hP hR) hR opened hk

/-- **`allI` of `impI` of `impE` of `allE` proves that `P` holds of some set**, in every
package that declares the rule constants. -/
theorem exIntroByRules_typed (covers : OverSetTheoryRules Q) {P a p : CTm (Head L) n}
    (hP : CTyped Q Γ P (.pi allSets cProp)) (ha : CTyped Q Γ a allSets)
    (hp : CTyped Q Γ p (cHolds (.app P a))) :
    CTyped Q Γ (exIntroByRules P a p) (cHolds (cEx allSets P)) := by
  let ΓR := Γ.snoc cProp
  let Γk := ΓR.snoc (cHolds (exWitnessAll P))
  let Γs := Γk.snoc allSets
  have motive := exMotive_typed covers.sets hP
  have motiveLam : CTyped Q Γ (.lam cProp (exMotive P)) (.pi cProp cProp) :=
    .lamIntro (prop_isClass covers.sets) (covers.sets.contains.isUniverse (.sort _))
      (classToClass_typed covers.sets.contains (prop_isClass covers.sets)
        (prop_isClass covers.sets))
      (covers.sets.contains.isUniverse (.sort _)) motive
  have body3 : CTyped Q Γs
      (cImp (.app (((P.rename wk).rename wk).rename wk) (.var 0)) (.var 2)) cProp :=
    cImp_typed covers.sets
      (.appElim (B := cProp)
        (((hP.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))).weaken (E := allSets))
        (CDerivable.var (P := Q) (Γ := Γs) 0))
      (CDerivable.var (P := Q) (Γ := Γs) 2)
  have bodyRen : CTyped Q Γs ((exPredBody P).rename (liftRen wk)) cProp := by
    have same : ((exPredBody P).rename (liftRen wk)) =
        cImp (.app (((P.rename wk).rename wk).rename wk) (.var 0)) (.var 2) := by
      unfold exPredBody
      show cImp (.app (CTm.rename (liftRen wk) ((P.rename wk).rename wk))
          (CTm.rename (liftRen wk) (.var 0)))
        (CTm.rename (liftRen wk) (.var 1)) = _
      rw [CTm.rename_liftRen_wk]
      rfl
    rw [same]
    exact body3
  have predBody : CTyped Q (ΓR.snoc allSets) (exPredBody P) cProp := by
    refine cImp_typed covers.sets ?_ (CDerivable.var (P := Q) (Γ := ΓR.snoc allSets) 1)
    exact .appElim (B := cProp) ((hP.weaken (E := cProp)).weaken (E := allSets))
      (CDerivable.var (P := Q) (Γ := ΓR.snoc allSets) 0)
  have predBase : CTyped Q ΓR (.lam allSets (exPredBody P)) (.pi allSets cProp) :=
    .lamIntro (sets_typed covers.sets.contains) (covers.sets.contains.isUniverse (.sort _))
      (classToClass_typed covers.sets.contains (sets_typed covers.sets.contains)
        (prop_isClass covers.sets))
      (covers.sets.contains.isUniverse (.sort _)) predBody
  have predW : CTyped Q Γk ((CTm.lam allSets (exPredBody P)).rename wk) (.pi allSets cProp) :=
    predBase.weaken (E := cHolds (exWitnessAll P))
  have kVar : CTyped Q Γk (.var 0)
      (cHolds (cAll allSets ((CTm.lam allSets (exPredBody P)).rename wk))) :=
    CDerivable.var (P := Q) (Γ := Γk) 0
  have a2 : CTyped Q Γk ((a.rename wk).rename wk) allSets :=
    (ha.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))
  have setsK : CTyped Q Γk allSets allClasses :=
    ((sets_typed covers.sets.contains).weaken (E := cProp)).weaken
      (E := cHolds (exWitnessAll P))
  have propS : CTyped Q Γs cProp allClasses :=
    (((prop_isClass covers.sets).weaken (E := cProp)).weaken
      (E := cHolds (exWitnessAll P))).weaken (E := allSets)
  have eliminated := cAllE_typed covers setsK predW kVar a2
  have beta : CEqual Q Γk
      (.app (.lam allSets ((exPredBody P).rename (liftRen wk))) ((a.rename wk).rename wk))
      (CTm.inst0 ((a.rename wk).rename wk) ((exPredBody P).rename (liftRen wk))) cProp :=
    .betaPi (B := cProp)
      (classToClass_typed covers.sets.contains setsK propS)
      (covers.sets.contains.isUniverse (.sort _)) bodyRen a2
  have opened : CTyped Q Γk
      (cAllE allSets ((CTm.lam allSets (exPredBody P)).rename wk) (.var 0)
        ((a.rename wk).rename wk))
      (cHolds (cImp (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) (.var 1))) := by
    rw [← exIntro_beta_prop]
    exact CDerivable.conv eliminated (cHolds_congr covers.sets beta)
      (covers.sets.contains.isUniverse (.sort _))
  have prem : CTyped Q Γk (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk)) cProp :=
    .appElim (B := cProp)
      ((hP.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))) a2
  have goalR : CTyped Q Γk (.var 1) cProp := CDerivable.var (P := Q) (Γ := Γk) 1
  have p2 : CTyped Q Γk ((p.rename wk).rename wk)
      (cHolds (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk))) :=
    (hp.weaken (E := cProp)).weaken (E := cHolds (exWitnessAll P))
  have impDone := cImpE_typed covers prem goalR opened p2
  have domainK : CTyped Q ΓR (cHolds (exWitnessAll P)) U0 :=
    cHolds_typed covers.sets (exWitnessAll_typed covers.sets hP)
  have codK : CTyped Q Γk (cHolds (.var 1)) U0 := cHolds_typed covers.sets goalR
  have inner := CDerivable.lamIntro domainK (covers.sets.contains.isUniverse (.sort _))
    (smallFunctions_typed covers.sets.contains domainK codK)
    (covers.sets.contains.isUniverse (.sort _)) impDone
  have asImp := cImpI_typed covers (exWitnessAll_typed covers.sets hP)
    (CDerivable.var (P := Q) (Γ := ΓR) 0) inner
  have shifted : CEqual Q ΓR (.app ((CTm.lam cProp (exMotive P)).rename wk) (.var 0))
      (exMotive P) cProp :=
    predicate_apply_var covers.sets (prop_isClass covers.sets) motive
  have bodyAll : CTyped Q ΓR
      (cImpI (exWitnessAll P) (.var 0)
        (.lam (cHolds (exWitnessAll P))
          (cImpE
            (.app ((P.rename wk).rename wk) ((a.rename wk).rename wk))
            (.var 1)
            (cAllE allSets ((CTm.lam allSets (exPredBody P)).rename wk) (.var 0)
              ((a.rename wk).rename wk))
            ((p.rename wk).rename wk))))
      (cHolds (.app ((CTm.lam cProp (exMotive P)).rename wk) (.var 0))) :=
    CDerivable.conv asImp (.symm (cHolds_congr covers.sets shifted))
      (covers.sets.contains.isUniverse (.sort _))
  have appProp : CTyped Q ΓR (.app ((CTm.lam cProp (exMotive P)).rename wk) (.var 0)) cProp :=
    .appElim (B := cProp) (motiveLam.weaken (E := cProp)) (CDerivable.var (P := Q) (Γ := ΓR) 0)
  have funLam := CDerivable.lamIntro (prop_isClass covers.sets)
    (covers.sets.contains.isUniverse (.sort _))
    (classToSet_typed covers.sets.contains (prop_isClass covers.sets)
      (cHolds_isSet covers.sets appProp))
    (covers.sets.contains.isUniverse (.sort _)) bodyAll
  exact cAllI_typed covers (prop_isClass covers.sets) motiveLam funLam

/-- **In the set theory on rule constants, the rule introduction proves that `P` holds of
some set.** -/
theorem setTheoryRules_exIntro_typed {P a p : CTm (Head L) 0}
    (hP : CTyped (setTheoryRules L) .nil P (.pi allSets cProp))
    (ha : CTyped (setTheoryRules L) .nil a allSets)
    (hp : CTyped (setTheoryRules L) .nil p (cHolds (.app P a))) :
    CTyped (setTheoryRules L) .nil (exIntroByRules P a p) (cHolds (cEx allSets P)) :=
  exIntroByRules_typed setTheoryRules_over hP ha hp

/-- **In the set theory on rule constants, an existential eliminates into any proposition.** -/
theorem setTheoryRules_exElim_typed {P h R k : CTm (Head L) 0}
    (hP : CTyped (setTheoryRules L) .nil P (.pi allSets cProp))
    (hR : CTyped (setTheoryRules L) .nil R cProp)
    (hh : CTyped (setTheoryRules L) .nil h (cHolds (cEx allSets P)))
    (hk : CTyped (setTheoryRules L) .nil k (cHolds (exElimPred P R))) :
    CTyped (setTheoryRules L) .nil (exElimByRules P h R k) (cHolds R) :=
  exElimByRules_typed setTheoryRules_over hP hR hh hk

/-! ### Two proofs of existence have one value -/

/-- The value of `allSets` is the set at level zero. -/
theorem ev_allSets {n : Nat} {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (ν : Nat → Above L) (ρ : Env.{u} n) :
    ev (chainHead V ground ν) consts (allSets : CTm (Head L) n) ρ = V (.above 0) := rfl

/-- The value of `cProp` is the value of the constant `prop`. -/
theorem ev_cProp {n : Nat} {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (ν : Nat → Above L) (ρ : Env.{u} n) :
    ev (chainHead V ground ν) consts (cProp : CTm (Head L) n) ρ = consts propN := rfl

omit [LevelOrder L] in
/-- The value of a function type is the set of trace functions into the values of the body. -/
theorem ev_pi {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) (ρ : Env.{u} n) :
    ev heads consts (.pi A B) ρ =
      tracePiSet (ev heads consts A ρ) (fun x => ev heads consts B (extend ρ x)) := rfl

/-- The value of `allSets` is a class. -/
theorem allSets_in_classes {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (ν : Nat → Above L) {consts : DeclName → ZFSet.{u}}
    (ρ : Env.{u} 0) :
    ev (chainHead V ground ν) consts allSets ρ ∈ V (.above 1) := by
  rw [ev_allSets ν ρ, ← Above.succ_above 0]
  exact chain.mem_succ (.above 0)

/-- **The value of an existential over the sets is the truth value of the statement**, in a
set model that reads the constants: a typed predicate takes sets to truth values. -/
theorem exHolds_truthCode
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot)
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q) {P : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp)) :
    ev (chainHead V ground ν) consts (cHolds (cEx allSets P)) Fin.elim0 =
      truthCode (∃ x ∈ ev (chainHead V ground ν) consts allSets Fin.elim0,
        (∅ : ZFSet.{u}) ∈ traceApp (ev (chainHead V ground ν) consts P Fin.elim0) x) := by
  have propClass : truthValues ∈ V (.above 1) :=
    ClosedChain.mono chain (Above.below_le_above LevelOrder.bot 1)
      (truthValues_mem_zero chain groundTyped)
  have inPi := CDerivable.inhabited model hP
  rw [ev_pi allSets cProp Fin.elim0] at inPi
  have value : ∀ x ∈ ev (chainHead V ground ν) consts allSets Fin.elim0,
      traceApp (ev (chainHead V ground ν) consts P Fin.elim0) x =
        truthCode ((∅ : ZFSet.{u}) ∈
          traceApp (ev (chainHead V ground ν) consts P Fin.elim0) x) := by
    intro x hx
    have memFibre := traceApp_mem_fibre inPi hx
    rw [ev_cProp ν (extend Fin.elim0 x), reads.prop] at memFibre
    exact (truthValue_eq memFibre).symm
  exact ev_cHolds reads
    (ev_cEx reads propClass (allSets_in_classes chain ν Fin.elim0) value)

/-- **Two proofs that `P` holds of some set have one value**: each is the member of the
truth value. -/
theorem exProofs_one_value
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot)
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q) {P hA hB : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp))
    (tA : CTyped Q .nil hA (cHolds (cEx allSets P)))
    (tB : CTyped Q .nil hB (cHolds (cEx allSets P))) :
    ev (chainHead V ground ν) consts hA Fin.elim0 =
      ev (chainHead V ground ν) consts hB Fin.elim0 := by
  have code := exHolds_truthCode chain groundTyped reads ν model hP
  have mA := CDerivable.inhabited model tA
  have mB := CDerivable.inhabited model tB
  rw [code] at mA
  rw [code] at mB
  exact ((mem_truthCode _ _).mp mA).1.trans ((mem_truthCode _ _).mp mB).1.symm

/-- **No function of a proof of existence returns both witnesses** when their values differ:
the two proofs have one value, so the function sends them to one set. -/
theorem no_existence_witness
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot)
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q)
    {P a b w hA hB : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp))
    (tA : CTyped Q .nil hA (cHolds (cEx allSets P)))
    (tB : CTyped Q .nil hB (cHolds (cEx allSets P)))
    (tw : CTyped Q .nil w (.pi (cHolds (cEx allSets P)) allSets))
    (diff : ev (chainHead V ground ν) consts a Fin.elim0 ≠
      ev (chainHead V ground ν) consts b Fin.elim0) :
    ¬ (traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
          (ev (chainHead V ground ν) consts hA Fin.elim0) =
        ev (chainHead V ground ν) consts a Fin.elim0 ∧
      traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
          (ev (chainHead V ground ν) consts hB Fin.elim0) =
        ev (chainHead V ground ν) consts b Fin.elim0) := by
  intro spec
  have same := exProofs_one_value chain groundTyped reads ν model hP tA tB
  have wPi := CDerivable.inhabited model tw
  rw [ev_pi (cHolds (cEx allSets P)) allSets Fin.elim0] at wPi
  have aMem := CDerivable.inhabited model tA
  have code := exHolds_truthCode chain groundTyped reads ν model hP
  rw [code] at aMem
  rw [code] at wPi
  have raw := traceApp_mem_fibre wPi aMem
  have fibre : traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
      (ev (chainHead V ground ν) consts hA Fin.elim0) ∈ V (.above 0) := by
    rw [ev_allSets (V := V) (ground := ground) (consts := consts) ν
      (extend Fin.elim0 (ev (chainHead V ground ν) consts hA Fin.elim0))] at raw
    exact raw
  have packed : traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
        (ev (chainHead V ground ν) consts hA Fin.elim0) =
      traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
        (ev (chainHead V ground ν) consts hB Fin.elim0) ∧
      traceApp (ev (chainHead V ground ν) consts w Fin.elim0)
        (ev (chainHead V ground ν) consts hA Fin.elim0) ∈ V (.above 0) :=
    ⟨congrArg (traceApp (ev (chainHead V ground ν) consts w Fin.elim0)) same, fibre⟩
  exact diff (spec.1.symm.trans (packed.1.trans spec.2))

/-- **In the set theory, no function of a proof of existence returns both witnesses** when
their values differ. -/
theorem setTheory_no_existence_witness
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u})
    {P a b w hA hB : CTm (Head L) 0}
    (hP : CTyped (setTheory L) .nil P (.pi allSets cProp))
    (tA : CTyped (setTheory L) .nil hA (cHolds (cEx allSets P)))
    (tB : CTyped (setTheory L) .nil hB (cHolds (cEx allSets P)))
    (tw : CTyped (setTheory L) .nil w (.pi (cHolds (cEx allSets P)) allSets))
    (diff : ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) a Fin.elim0 ≠
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) b Fin.elim0) :
    ¬ (traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) hA Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) a Fin.elim0 ∧
      traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) hB Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) b Fin.elim0) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (setDecls L)
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    fun _ declared => familyConsts_declared declared
  exact no_existence_witness chain groundTyped reads ν
    (setTheory_setModel chain groundTyped aroundMem ν base) hP tA tB tw diff

/-- **In the set theory on rule constants, no function of a proof of existence returns both
witnesses** when their values differ. -/
theorem setTheoryRules_no_existence_witness
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u})
    {P a b w hA hB : CTm (Head L) 0}
    (hP : CTyped (setTheoryRules L) .nil P (.pi allSets cProp))
    (tA : CTyped (setTheoryRules L) .nil hA (cHolds (cEx allSets P)))
    (tB : CTyped (setTheoryRules L) .nil hB (cHolds (cEx allSets P)))
    (tw : CTyped (setTheoryRules L) .nil w (.pi (cHolds (cEx allSets P)) allSets))
    (diff : ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) a Fin.elim0 ≠
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) b Fin.elim0) :
    ¬ (traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) hA Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) a Fin.elim0 ∧
      traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) hB Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) b Fin.elim0) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    reads_of_rulesTable fun _ declared => familyConsts_declared declared
  exact no_existence_witness chain groundTyped reads ν
    (setTheoryRules_setModel chain groundTyped aroundMem ν base) hP tA tB tw diff

/-! ### The two introductions of a disjunction -/

/-- `(p → r) → (q → r) → r`, the body of a disjunction. -/
def orMotive (p q : CTm (Head L) n) : CTm (Head L) (n + 1) :=
  cImp (cImp (p.rename wk) (.var 0)) (cImp (cImp (q.rename wk) (.var 0)) (.var 0))

omit [LevelOrder L] in
/-- A disjunction is the quantification of its motive. -/
theorem cOr_motive (p q : CTm (Head L) n) :
    cOr p q = cAll cProp (CTm.lam cProp (orMotive p q)) := by
  unfold cOr orMotive
  rfl

omit [LevelOrder L] in
/-- The conclusion of a disjunction, under its first proof, is the second implication. -/
theorem orConcl_rename (q : CTm (Head L) n) :
    (cImp (cImp (q.rename wk) (.var 0)) (.var 0)).rename wk =
      cImp (cImp ((q.rename wk).rename wk) (.var 1)) (.var 1) := rfl

/-- **The left introduction of a disjunction**: from a proof of `p`,
`λ r. λ (l : p → r). λ (_ : q → r). l h`. -/
def orIntroLeft (ops : ProofOps L) (p q h : CTm (Head L) n) : CTm (Head L) n :=
  ops.allI cProp (orMotive p q)
    (ops.impI (cImp (p.rename wk) (.var 0))
      (cImp (cImp (q.rename wk) (.var 0)) (.var 0))
      (ops.impI (cImp ((q.rename wk).rename wk) (.var 1)) (.var 1)
        (ops.impE (((p.rename wk).rename wk).rename wk) (.var 2) (.var 1)
          (((h.rename wk).rename wk).rename wk))))

/-- **The right introduction of a disjunction**: from a proof of `q`,
`λ r. λ (_ : p → r). λ (right : q → r). right h`. -/
def orIntroRight (ops : ProofOps L) (p q h : CTm (Head L) n) : CTm (Head L) n :=
  ops.allI cProp (orMotive p q)
    (ops.impI (cImp (p.rename wk) (.var 0))
      (cImp (cImp (q.rename wk) (.var 0)) (.var 0))
      (ops.impI (cImp ((q.rename wk).rename wk) (.var 1)) (.var 1)
        (ops.impE (((q.rename wk).rename wk).rename wk) (.var 2) (.var 0)
          (((h.rename wk).rename wk).rename wk))))

/-- **The left introduction proves the disjunction**, in either presentation of the proofs. -/
theorem orIntroLeft_typed {ops : ProofOps L} (lawful : ops.Lawful Q) (covers : OverSetTheory Q)
    {p q h : CTm (Head L) n} (hp : CTyped Q Γ p cProp) (hq : CTyped Q Γ q cProp)
    (hh : CTyped Q Γ h (cHolds p)) :
    CTyped Q Γ (orIntroLeft ops p q h) (cHolds (cOr p q)) := by
  let Γ1 : CCtx (Head L) (n + 1) := Γ.snoc cProp
  let prem : CTm (Head L) (n + 1) := cImp (p.rename wk) (.var 0)
  let concl : CTm (Head L) (n + 1) := cImp (cImp (q.rename wk) (.var 0)) (.var 0)
  let Γ2 : CCtx (Head L) (n + 2) := Γ1.snoc (cHolds prem)
  let prem2 : CTm (Head L) (n + 2) := cImp ((q.rename wk).rename wk) (.var 1)
  let Γ3 : CCtx (Head L) (n + 3) := Γ2.snoc (cHolds prem2)
  have p1 : CTyped Q Γ1 (p.rename wk) cProp := hp.weaken (E := cProp)
  have q1 : CTyped Q Γ1 (q.rename wk) cProp := hq.weaken (E := cProp)
  have r1 : CTyped Q Γ1 (.var 0) cProp := CDerivable.var (P := Q) (Γ := Γ1) 0
  have premTy : CTyped Q Γ1 prem cProp := cImp_typed covers p1 r1
  have qImp : CTyped Q Γ1 (cImp (q.rename wk) (.var 0)) cProp := cImp_typed covers q1 r1
  have conclTy : CTyped Q Γ1 concl cProp := cImp_typed covers qImp r1
  have motive : CTyped Q Γ1 (orMotive p q) cProp := by
    unfold orMotive
    exact cImp_typed covers premTy conclTy
  have q2 : CTyped Q Γ2 ((q.rename wk).rename wk) cProp := q1.weaken (E := cHolds prem)
  have r2 : CTyped Q Γ2 (.var 1) cProp := CDerivable.var (P := Q) (Γ := Γ2) 1
  have prem2Ty : CTyped Q Γ2 prem2 cProp := cImp_typed covers q2 r2
  have p3 : CTyped Q Γ3 (((p.rename wk).rename wk).rename wk) cProp :=
    (p1.weaken (E := cHolds prem)).weaken (E := cHolds prem2)
  have r3 : CTyped Q Γ3 (.var 2) cProp := CDerivable.var (P := Q) (Γ := Γ3) 2
  have f3 : CTyped Q Γ3 (.var 1)
      (cHolds (cImp (((p.rename wk).rename wk).rename wk) (.var 2))) :=
    CDerivable.var (P := Q) (Γ := Γ3) 1
  have h3 : CTyped Q Γ3 (((h.rename wk).rename wk).rename wk)
      (cHolds (((p.rename wk).rename wk).rename wk)) :=
    ((hh.weaken (E := cProp)).weaken (E := cHolds prem)).weaken (E := cHolds prem2)
  have use := lawful.impE p3 r3 f3 h3
  have step2 := lawful.impI prem2Ty r2 use
  have step2At : CTyped Q Γ2
      (ops.impI prem2 (.var 1)
        (ops.impE (((p.rename wk).rename wk).rename wk) (.var 2) (.var 1)
          (((h.rename wk).rename wk).rename wk)))
      (cHolds (concl.rename wk)) := by
    rw [orConcl_rename q]
    exact step2
  have step1 := lawful.impI premTy conclTy step2At
  have step1At : CTyped Q Γ1
      (ops.impI prem concl
        (ops.impI prem2 (.var 1)
          (ops.impE (((p.rename wk).rename wk).rename wk) (.var 2) (.var 1)
            (((h.rename wk).rename wk).rename wk))))
      (cHolds (orMotive p q)) := by
    unfold orMotive
    exact step1
  have done := lawful.allI (prop_isClass covers) motive step1At
  rw [← cOr_motive p q] at done
  unfold orIntroLeft
  exact done

/-- **The right introduction proves the disjunction**, in either presentation of the proofs. -/
theorem orIntroRight_typed {ops : ProofOps L} (lawful : ops.Lawful Q) (covers : OverSetTheory Q)
    {p q h : CTm (Head L) n} (hp : CTyped Q Γ p cProp) (hq : CTyped Q Γ q cProp)
    (hh : CTyped Q Γ h (cHolds q)) :
    CTyped Q Γ (orIntroRight ops p q h) (cHolds (cOr p q)) := by
  let Γ1 : CCtx (Head L) (n + 1) := Γ.snoc cProp
  let prem : CTm (Head L) (n + 1) := cImp (p.rename wk) (.var 0)
  let concl : CTm (Head L) (n + 1) := cImp (cImp (q.rename wk) (.var 0)) (.var 0)
  let Γ2 : CCtx (Head L) (n + 2) := Γ1.snoc (cHolds prem)
  let prem2 : CTm (Head L) (n + 2) := cImp ((q.rename wk).rename wk) (.var 1)
  let Γ3 : CCtx (Head L) (n + 3) := Γ2.snoc (cHolds prem2)
  have p1 : CTyped Q Γ1 (p.rename wk) cProp := hp.weaken (E := cProp)
  have q1 : CTyped Q Γ1 (q.rename wk) cProp := hq.weaken (E := cProp)
  have r1 : CTyped Q Γ1 (.var 0) cProp := CDerivable.var (P := Q) (Γ := Γ1) 0
  have premTy : CTyped Q Γ1 prem cProp := cImp_typed covers p1 r1
  have qImp : CTyped Q Γ1 (cImp (q.rename wk) (.var 0)) cProp := cImp_typed covers q1 r1
  have conclTy : CTyped Q Γ1 concl cProp := cImp_typed covers qImp r1
  have motive : CTyped Q Γ1 (orMotive p q) cProp := by
    unfold orMotive
    exact cImp_typed covers premTy conclTy
  have q2 : CTyped Q Γ2 ((q.rename wk).rename wk) cProp := q1.weaken (E := cHolds prem)
  have r2 : CTyped Q Γ2 (.var 1) cProp := CDerivable.var (P := Q) (Γ := Γ2) 1
  have prem2Ty : CTyped Q Γ2 prem2 cProp := cImp_typed covers q2 r2
  have q3 : CTyped Q Γ3 (((q.rename wk).rename wk).rename wk) cProp :=
    (q2.weaken (E := cHolds prem2))
  have r3 : CTyped Q Γ3 (.var 2) cProp := CDerivable.var (P := Q) (Γ := Γ3) 2
  have f0 : CTyped Q Γ3 (.var 0)
      (cHolds (cImp (((q.rename wk).rename wk).rename wk) (.var 2))) :=
    CDerivable.var (P := Q) (Γ := Γ3) 0
  have h3 : CTyped Q Γ3 (((h.rename wk).rename wk).rename wk)
      (cHolds (((q.rename wk).rename wk).rename wk)) :=
    ((hh.weaken (E := cProp)).weaken (E := cHolds prem)).weaken (E := cHolds prem2)
  have use := lawful.impE q3 r3 f0 h3
  have step2 := lawful.impI prem2Ty r2 use
  have step2At : CTyped Q Γ2
      (ops.impI prem2 (.var 1)
        (ops.impE (((q.rename wk).rename wk).rename wk) (.var 2) (.var 0)
          (((h.rename wk).rename wk).rename wk)))
      (cHolds (concl.rename wk)) := by
    rw [orConcl_rename q]
    exact step2
  have step1 := lawful.impI premTy conclTy step2At
  have step1At : CTyped Q Γ1
      (ops.impI prem concl
        (ops.impI prem2 (.var 1)
          (ops.impE (((q.rename wk).rename wk).rename wk) (.var 2) (.var 0)
            (((h.rename wk).rename wk).rename wk))))
      (cHolds (orMotive p q)) := by
    unfold orMotive
    exact step1
  have done := lawful.allI (prop_isClass covers) motive step1At
  rw [← cOr_motive p q] at done
  unfold orIntroRight
  exact done

/-! ### `Empty` or the power set of `Empty` -/

/-- `x = Empty ∨ x = Power Empty`. -/
def emptyOrBody : CTm (Head L) 1 :=
  cOr (cEq allSets (.var 0) cEmpty) (cEq allSets (.var 0) (cPower cEmpty))

/-- The predicate `λ x. x = Empty ∨ x = Power Empty`. -/
def emptyOrPower : CTm (Head L) 0 := .lam allSets emptyOrBody

/-- **A proof that `Empty` equals `Empty`, injected on the left.** -/
def emptyOrLeftEq : CTm (Head L) 0 :=
  orIntroLeft equationOps (cEq allSets cEmpty cEmpty) (cEq allSets cEmpty (cPower cEmpty))
    (.refl cEmpty)

/-- **A proof that `Power Empty` equals itself, injected on the right.** -/
def emptyOrRightEq : CTm (Head L) 0 :=
  orIntroRight equationOps (cEq allSets (cPower cEmpty) cEmpty)
    (cEq allSets (cPower cEmpty) (cPower cEmpty)) (.refl (cPower cEmpty))

/-- **The same left proof, by the rule constants.** -/
def emptyOrLeftRule : CTm (Head L) 0 :=
  orIntroLeft ruleOps (cEq allSets cEmpty cEmpty) (cEq allSets cEmpty (cPower cEmpty))
    (cEqI allSets cEmpty cEmpty (.refl cEmpty))

/-- **The same right proof, by the rule constants.** -/
def emptyOrRightRule : CTm (Head L) 0 :=
  orIntroRight ruleOps (cEq allSets (cPower cEmpty) cEmpty)
    (cEq allSets (cPower cEmpty) (cPower cEmpty))
    (cEqI allSets (cPower cEmpty) (cPower cEmpty) (.refl (cPower cEmpty)))

/-- **The body of `λ x. x = Empty ∨ x = Power Empty` is a proposition.** -/
theorem emptyOrBody_typed (covers : OverSetTheory Q) :
    CTyped Q (.snoc .nil allSets) emptyOrBody cProp := by
  have sets : CTyped Q (.snoc .nil allSets) allSets allClasses :=
    sets_typed (Γ := .snoc .nil allSets) covers.contains
  have x : CTyped Q (.snoc .nil allSets) (.var 0) allSets :=
    CDerivable.var (P := Q) (Γ := .snoc .nil allSets) 0
  have e : CTyped Q (.snoc .nil allSets) cEmpty allSets :=
    empty_typed (Γ := .snoc .nil allSets) covers
  have pe : CTyped Q (.snoc .nil allSets) (cPower cEmpty) allSets :=
    powerEmpty_typed (Γ := .snoc .nil allSets) covers
  exact cOr_typed (Γ := .snoc .nil allSets) covers
    (cEq_typed (Γ := .snoc .nil allSets) covers sets x e)
    (cEq_typed (Γ := .snoc .nil allSets) covers sets x pe)

/-- **`λ x. x = Empty ∨ x = Power Empty` is a predicate on the sets.** -/
theorem emptyOrPower_typed (covers : OverSetTheory Q) :
    CTyped Q .nil emptyOrPower (.pi allSets cProp) :=
  .lamIntro (sets_typed (Γ := .nil) covers.contains) (covers.contains.isUniverse (.sort _))
    (classToClass_typed covers.contains (sets_typed (Γ := .nil) covers.contains)
      (prop_isClass (Γ := .snoc .nil allSets) covers))
    (covers.contains.isUniverse (.sort _)) (emptyOrBody_typed covers)

omit [LevelOrder L] in
/-- Opening the disjunction at a set is the disjunction at that set. -/
theorem inst0_emptyOrBody (a : CTm (Head L) 0) :
    CTm.inst0 a emptyOrBody =
      cOr (cEq allSets a cEmpty) (cEq allSets a (cPower cEmpty)) := by
  unfold emptyOrBody cOr
  rw [show CTm.inst0 a (cAll cProp (.lam cProp
        (cImp (cImp ((cEq allSets (.var 0) cEmpty).rename wk) (.var 0))
          (cImp (cImp ((cEq allSets (.var 0) (cPower cEmpty)).rename wk) (.var 0))
            (.var 0))))) =
      cAll cProp (.lam cProp
        (cImp
          (cImp (CTm.subst (CTm.liftSub (CTm.subst0 a))
              ((cEq allSets (.var 0) cEmpty).rename wk))
            (.var 0))
          (cImp
            (cImp (CTm.subst (CTm.liftSub (CTm.subst0 a))
                ((cEq allSets (.var 0) (cPower cEmpty)).rename wk))
              (.var 0))
            (.var 0)))) from rfl]
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]
  rfl

include computes

/-- **Where the equations make the proofs functions, `Empty` satisfies the predicate.** -/
theorem emptyOr_at_empty_typed (covers : OverSetTheory Q) :
    CTyped Q .nil emptyOrLeftEq (cHolds (.app emptyOrPower cEmpty)) := by
  have orTy := orIntroLeft_typed (Γ := .nil) (equationOps_lawful covers computes) covers
    (cEq_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (empty_typed (Γ := .nil) covers) (empty_typed (Γ := .nil) covers))
    (cEq_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (empty_typed (Γ := .nil) covers) (powerEmpty_typed (Γ := .nil) covers))
    (eqRefl_typed computes (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (empty_typed (Γ := .nil) covers))
  have beta := CDerivable.betaPi (B := cProp)
    (classToClass_typed covers.contains (sets_typed (Γ := .nil) covers.contains)
      (prop_isClass (Γ := .snoc .nil allSets) covers))
    (covers.contains.isUniverse (.sort _)) (emptyOrBody_typed covers)
    (empty_typed (Γ := .nil) covers)
  have opened : CEqual Q .nil (.app emptyOrPower cEmpty)
      (cOr (cEq allSets cEmpty cEmpty) (cEq allSets cEmpty (cPower cEmpty))) cProp := by
    rw [inst0_emptyOrBody] at beta
    exact beta
  exact CDerivable.conv orTy (cHolds_congr covers opened.symm)
    (covers.contains.isUniverse (.sort _))

/-- **Where the equations make the proofs functions, `Power Empty` satisfies the predicate.** -/
theorem emptyOr_at_power_typed (covers : OverSetTheory Q) :
    CTyped Q .nil emptyOrRightEq (cHolds (.app emptyOrPower (cPower cEmpty))) := by
  have orTy := orIntroRight_typed (Γ := .nil) (equationOps_lawful covers computes) covers
    (cEq_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (powerEmpty_typed (Γ := .nil) covers) (empty_typed (Γ := .nil) covers))
    (cEq_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (powerEmpty_typed (Γ := .nil) covers) (powerEmpty_typed (Γ := .nil) covers))
    (eqRefl_typed computes (Γ := .nil) covers (sets_typed (Γ := .nil) covers.contains)
      (powerEmpty_typed (Γ := .nil) covers))
  have beta := CDerivable.betaPi (B := cProp)
    (classToClass_typed covers.contains (sets_typed (Γ := .nil) covers.contains)
      (prop_isClass (Γ := .snoc .nil allSets) covers))
    (covers.contains.isUniverse (.sort _)) (emptyOrBody_typed covers)
    (powerEmpty_typed (Γ := .nil) covers)
  have opened : CEqual Q .nil (.app emptyOrPower (cPower cEmpty))
      (cOr (cEq allSets (cPower cEmpty) cEmpty)
        (cEq allSets (cPower cEmpty) (cPower cEmpty))) cProp := by
    rw [inst0_emptyOrBody] at beta
    exact beta
  exact CDerivable.conv orTy (cHolds_congr covers opened.symm)
    (covers.contains.isUniverse (.sort _))

omit computes

/-- **By the rule constants, `Empty` satisfies the predicate.** -/
theorem emptyOr_at_empty_rules (covers : OverSetTheoryRules Q) :
    CTyped Q .nil emptyOrLeftRule (cHolds (.app emptyOrPower cEmpty)) := by
  have orTy := orIntroLeft_typed (Γ := .nil) (ruleOps_lawful covers) covers.sets
    (cEq_typed (Γ := .nil) covers.sets (sets_typed (Γ := .nil) covers.sets.contains)
      (empty_typed (Γ := .nil) covers.sets) (empty_typed (Γ := .nil) covers.sets))
    (cEq_typed (Γ := .nil) covers.sets (sets_typed (Γ := .nil) covers.sets.contains)
      (empty_typed (Γ := .nil) covers.sets) (powerEmpty_typed (Γ := .nil) covers.sets))
    (eqIRefl_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.sets.contains)
      (empty_typed (Γ := .nil) covers.sets))
  have beta := CDerivable.betaPi (B := cProp)
    (classToClass_typed covers.sets.contains (sets_typed (Γ := .nil) covers.sets.contains)
      (prop_isClass (Γ := .snoc .nil allSets) covers.sets))
    (covers.sets.contains.isUniverse (.sort _)) (emptyOrBody_typed covers.sets)
    (empty_typed (Γ := .nil) covers.sets)
  have opened : CEqual Q .nil (.app emptyOrPower cEmpty)
      (cOr (cEq allSets cEmpty cEmpty) (cEq allSets cEmpty (cPower cEmpty))) cProp := by
    rw [inst0_emptyOrBody] at beta
    exact beta
  exact CDerivable.conv orTy (cHolds_congr covers.sets opened.symm)
    (covers.sets.contains.isUniverse (.sort _))

/-- **By the rule constants, `Power Empty` satisfies the predicate.** -/
theorem emptyOr_at_power_rules (covers : OverSetTheoryRules Q) :
    CTyped Q .nil emptyOrRightRule (cHolds (.app emptyOrPower (cPower cEmpty))) := by
  have orTy := orIntroRight_typed (Γ := .nil) (ruleOps_lawful covers) covers.sets
    (cEq_typed (Γ := .nil) covers.sets (sets_typed (Γ := .nil) covers.sets.contains)
      (powerEmpty_typed (Γ := .nil) covers.sets) (empty_typed (Γ := .nil) covers.sets))
    (cEq_typed (Γ := .nil) covers.sets (sets_typed (Γ := .nil) covers.sets.contains)
      (powerEmpty_typed (Γ := .nil) covers.sets) (powerEmpty_typed (Γ := .nil) covers.sets))
    (eqIRefl_typed (Γ := .nil) covers (sets_typed (Γ := .nil) covers.sets.contains)
      (powerEmpty_typed (Γ := .nil) covers.sets))
  have beta := CDerivable.betaPi (B := cProp)
    (classToClass_typed covers.sets.contains (sets_typed (Γ := .nil) covers.sets.contains)
      (prop_isClass (Γ := .snoc .nil allSets) covers.sets))
    (covers.sets.contains.isUniverse (.sort _)) (emptyOrBody_typed covers.sets)
    (powerEmpty_typed (Γ := .nil) covers.sets)
  have opened : CEqual Q .nil (.app emptyOrPower (cPower cEmpty))
      (cOr (cEq allSets (cPower cEmpty) cEmpty)
        (cEq allSets (cPower cEmpty) (cPower cEmpty))) cProp := by
    rw [inst0_emptyOrBody] at beta
    exact beta
  exact CDerivable.conv orTy (cHolds_congr covers.sets opened.symm)
    (covers.sets.contains.isUniverse (.sort _))

/-- **In the set theory, `λ R k. k Empty p` proves that the predicate holds of some set.** -/
theorem setTheory_emptyOr_ex_empty :
    CTyped (setTheory L) .nil (exIntro emptyOrPower cEmpty emptyOrLeftEq)
      (cHolds (cEx allSets emptyOrPower)) :=
  setTheory_exIntro_typed (emptyOrPower_typed setTheory_over) (empty_typed setTheory_over)
    (emptyOr_at_empty_typed setTheory_steps setTheory_over)

/-- **In the set theory, `λ R k. k (Power Empty) q` proves the same existential.** -/
theorem setTheory_emptyOr_ex_power :
    CTyped (setTheory L) .nil (exIntro emptyOrPower (cPower cEmpty) emptyOrRightEq)
      (cHolds (cEx allSets emptyOrPower)) :=
  setTheory_exIntro_typed (emptyOrPower_typed setTheory_over)
    (powerEmpty_typed setTheory_over)
    (emptyOr_at_power_typed setTheory_steps setTheory_over)

/-- **In the set theory on rule constants, the rule introduction at `Empty` proves the
existential.** -/
theorem setTheoryRules_emptyOr_ex_empty :
    CTyped (setTheoryRules L) .nil (exIntroByRules emptyOrPower cEmpty emptyOrLeftRule)
      (cHolds (cEx allSets emptyOrPower)) :=
  setTheoryRules_exIntro_typed (emptyOrPower_typed setTheoryRules_over.sets)
    (empty_typed setTheoryRules_over.sets) (emptyOr_at_empty_rules setTheoryRules_over)

/-- **In the set theory on rule constants, the rule introduction at `Power Empty` proves the
existential.** -/
theorem setTheoryRules_emptyOr_ex_power :
    CTyped (setTheoryRules L) .nil
      (exIntroByRules emptyOrPower (cPower cEmpty) emptyOrRightRule)
      (cHolds (cEx allSets emptyOrPower)) :=
  setTheoryRules_exIntro_typed (emptyOrPower_typed setTheoryRules_over.sets)
    (powerEmpty_typed setTheoryRules_over.sets) (emptyOr_at_power_rules setTheoryRules_over)

/-- **`Empty` and `Power Empty` have different values**: the empty set is a member of the
power set of the empty set. -/
theorem empty_ne_power
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot)
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L) :
    ev (chainHead V ground ν) consts cEmpty Fin.elim0 ≠
      ev (chainHead V ground ν) consts (cPower cEmpty) Fin.elim0 := by
  intro same
  have emptyVal : ev (chainHead V ground ν) consts (cEmpty : CTm (Head L) 0) Fin.elim0 =
      (∅ : ZFSet.{u}) := by
    show consts emptyN = _
    exact reads.empty
  have powerVal : ev (chainHead V ground ν) consts (cPower cEmpty : CTm (Head L) 0) Fin.elim0 =
      ZFSet.powerset (∅ : ZFSet.{u}) := by
    show traceApp (consts powerN) (consts emptyN) = _
    rw [reads.power, reads.empty]
    exact opValue_apply _ (empty_mem_all chain groundTyped)
  have memPower : (∅ : ZFSet.{u}) ∈
      ev (chainHead V ground ν) consts (cPower cEmpty) Fin.elim0 := by
    rw [powerVal]
    exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← same, emptyVal] at memPower
  exact ZFSet.notMem_empty _ memPower

/-- **In the set theory the negative statement is not vacuous**: `Empty` and `Power Empty`
both witness `λ x. x = Empty ∨ x = Power Empty`, and their values differ, so no function of
the proof returns both. -/
theorem setTheory_emptyOr_no_witness
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) {w : CTm (Head L) 0}
    (tw : CTyped (setTheory L) .nil w (.pi (cHolds (cEx allSets emptyOrPower)) allSets)) :
    ¬ (traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntro emptyOrPower cEmpty emptyOrLeftEq) Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) cEmpty Fin.elim0 ∧
      traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntro emptyOrPower (cPower cEmpty) emptyOrRightEq) Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) (cPower cEmpty) Fin.elim0) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (setDecls L)
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    fun _ declared => familyConsts_declared declared
  exact setTheory_no_existence_witness chain groundTyped aroundMem ν base
    (emptyOrPower_typed setTheory_over) setTheory_emptyOr_ex_empty setTheory_emptyOr_ex_power tw
    (empty_ne_power chain groundTyped reads ν)

/-- **In the set theory on rule constants the negative statement is not vacuous**, for the
same predicate and the two rule introductions. -/
theorem setTheoryRules_emptyOr_no_witness
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) {w : CTm (Head L) 0}
    (tw : CTyped (setTheoryRules L) .nil w
      (.pi (cHolds (cEx allSets emptyOrPower)) allSets)) :
    ¬ (traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntroByRules emptyOrPower cEmpty emptyOrLeftRule) Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) cEmpty Fin.elim0 ∧
      traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around)) w Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntroByRules emptyOrPower (cPower cEmpty) emptyOrRightRule) Fin.elim0) =
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) (cPower cEmpty) Fin.elim0) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    reads_of_rulesTable fun _ declared => familyConsts_declared declared
  exact setTheoryRules_no_existence_witness chain groundTyped aroundMem ν base
    (emptyOrPower_typed setTheoryRules_over.sets) setTheoryRules_emptyOr_ex_empty
    setTheoryRules_emptyOr_ex_power tw (empty_ne_power chain groundTyped reads ν)

/-! ### `λ h. Eps P` returns one set -/

/-- **`λ h. Eps P`**, a function of a proof of existence. -/
def epsAsWitness (P : CTm (Head L) 0) : CTm (Head L) 0 :=
  .lam (cHolds (cEx allSets P)) (cEps (P.rename wk))

/-- **`λ h. Eps P` has the type of a function from a proof of existence to a set**, in either
package. -/
theorem epsAsWitness_typed (covers : OverSetTheory Q) {P : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp)) :
    CTyped Q .nil (epsAsWitness P) (.pi (cHolds (cEx allSets P)) allSets) := by
  have propTy : CTyped Q .nil (cEx allSets P) cProp :=
    cEx_typed covers (sets_typed (Γ := .nil) covers.contains) hP
  have domainU : CTyped Q .nil (cHolds (cEx allSets P)) U0 := cHolds_typed covers propTy
  have domainSet : CTyped Q .nil (cHolds (cEx allSets P)) allSets := cHolds_isSet covers propTy
  have cod : CTyped Q (.snoc .nil (cHolds (cEx allSets P))) allSets allClasses :=
    (sets_typed (Γ := .nil) covers.contains).weaken (E := cHolds (cEx allSets P))
  have body : CTyped Q (.snoc .nil (cHolds (cEx allSets P))) (cEps (P.rename wk)) allSets :=
    cEps_typed covers (hP.weaken (E := cHolds (cEx allSets P)))
  exact .lamIntro domainU (covers.contains.isUniverse (.sort _))
    (setToClass_typed covers.contains domainSet cod) (covers.contains.isUniverse (.sort _)) body

omit [LevelOrder L] in
/-- The value of an abstraction is the trace of its graph. -/
theorem ev_lam {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    {n : Nat} (A : CTm Head n) (body : CTm Head (n + 1)) (ρ : Env.{u} n) :
    ev heads consts (.lam A body) ρ =
      traceLam (graph (ev heads consts A ρ) (fun x => ev heads consts body (extend ρ x))) := rfl

/-- **A typed predicate on the sets denotes a trace function into the truth values.** -/
theorem predicate_mem_truth
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}}
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q) {P : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp)) :
    ev (chainHead V ground ν) consts P Fin.elim0 ∈
      tracePiSet (V (.above 0)) (fun _ => truthValues) := by
  have inPi := CDerivable.inhabited model hP
  rw [ev_pi allSets cProp Fin.elim0] at inPi
  have fibres : (fun x => ev (chainHead V ground ν) consts cProp (extend Fin.elim0 x)) =
      fun _ => truthValues := by
    funext x
    rw [ev_cProp ν (extend Fin.elim0 x), reads.prop]
  rw [fibres] at inPi
  rw [ev_allSets (V := V) (ground := ground) (consts := consts) ν Fin.elim0] at inPi
  exact inPi

/-- **`λ h. Eps P` returns `epsChoice` at every proof.** -/
theorem epsAsWitness_value
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}}
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q) {P h : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp))
    (th : CTyped Q .nil h (cHolds (cEx allSets P))) :
    traceApp (ev (chainHead V ground ν) consts (epsAsWitness P) Fin.elim0)
        (ev (chainHead V ground ν) consts h Fin.elim0) =
      epsChoice (V (.above 0)) (ev (chainHead V ground ν) consts P Fin.elim0) := by
  have hMem := CDerivable.inhabited model th
  have applied := traceApp_graph_beta
    (fun x => ev (chainHead V ground ν) consts (cEps (P.rename wk)) (extend Fin.elim0 x)) hMem
  rw [← ev_lam (cHolds (cEx allSets P)) (cEps (P.rename wk)) Fin.elim0] at applied
  have shifted : ev (chainHead V ground ν) consts (cEps (P.rename wk))
      (extend Fin.elim0 (ev (chainHead V ground ν) consts h Fin.elim0)) =
      traceApp (consts epsN) (ev (chainHead V ground ν) consts P Fin.elim0) := by
    show traceApp (consts epsN)
        (ev (chainHead V ground ν) consts (P.rename wk)
          (extend Fin.elim0 (ev (chainHead V ground ν) consts h Fin.elim0))) = _
    rw [ev_rename_wk (chainHead V ground ν) consts P Fin.elim0
      (ev (chainHead V ground ν) consts h Fin.elim0)]
  rw [shifted, reads.eps, epsValue_apply (predicate_mem_truth reads ν model hP)] at applied
  exact applied

/-- **`λ h. Eps P` fails the specification of a witness at one of two sets** whose values
differ: both applications return `epsChoice`, so one of them differs from the witness. -/
theorem epsAsWitness_misses
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}}
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (ν : Nat → Above L)
    (model : SetModel (chainHead V ground ν) consts Q) {P a b hA hB : CTm (Head L) 0}
    (hP : CTyped Q .nil P (.pi allSets cProp))
    (tA : CTyped Q .nil hA (cHolds (cEx allSets P)))
    (tB : CTyped Q .nil hB (cHolds (cEx allSets P)))
    (diff : ev (chainHead V ground ν) consts a Fin.elim0 ≠
      ev (chainHead V ground ν) consts b Fin.elim0) :
    traceApp (ev (chainHead V ground ν) consts (epsAsWitness P) Fin.elim0)
        (ev (chainHead V ground ν) consts hA Fin.elim0) ≠
      ev (chainHead V ground ν) consts a Fin.elim0 ∨
    traceApp (ev (chainHead V ground ν) consts (epsAsWitness P) Fin.elim0)
        (ev (chainHead V ground ν) consts hB Fin.elim0) ≠
      ev (chainHead V ground ν) consts b Fin.elim0 := by
  have zA := epsAsWitness_value reads ν model hP tA
  have zB := epsAsWitness_value reads ν model hP tB
  cases Classical.em (epsChoice (V (.above 0))
      (ev (chainHead V ground ν) consts P Fin.elim0) =
      ev (chainHead V ground ν) consts a Fin.elim0) with
  | inl sameA =>
    refine Or.inr ?_
    intro sameB
    exact diff (sameA.symm.trans (zB.symm.trans sameB))
  | inr diffA =>
    exact Or.inl fun sameApp => diffA (zA.symm.trans sameApp)

/-- **In the set theory, `λ h. Eps (λ x. x = Empty ∨ x = Power Empty)` fails at one of the
two witnesses.** -/
theorem setTheory_epsAsWitness_misses
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) :
    traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (epsAsWitness emptyOrPower) Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntro emptyOrPower cEmpty emptyOrLeftEq) Fin.elim0) ≠
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) cEmpty Fin.elim0 ∨
    traceApp (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (epsAsWitness emptyOrPower) Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (setDecls L)
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntro emptyOrPower (cPower cEmpty) emptyOrRightEq) Fin.elim0) ≠
      ev (chainHead V ground ν)
        (familyConsts base (setDecls L)
          (setValues (V (.above 0)) (V (.above 1)) around)) (cPower cEmpty) Fin.elim0 := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (setDecls L)
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    fun _ declared => familyConsts_declared declared
  exact epsAsWitness_misses reads ν (setTheory_setModel chain groundTyped aroundMem ν base)
    (emptyOrPower_typed setTheory_over) setTheory_emptyOr_ex_empty setTheory_emptyOr_ex_power
    (empty_ne_power chain groundTyped reads ν)

/-- **In the set theory on rule constants, `λ h. Eps (λ x. x = Empty ∨ x = Power Empty)` fails
at one of the two witnesses.** -/
theorem setTheoryRules_epsAsWitness_misses
    {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
    (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
    (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) :
    traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (epsAsWitness emptyOrPower) Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntroByRules emptyOrPower cEmpty emptyOrLeftRule) Fin.elim0) ≠
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) cEmpty Fin.elim0 ∨
    traceApp (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (epsAsWitness emptyOrPower) Fin.elim0)
        (ev (chainHead V ground ν)
          (familyConsts base (tableLookup (rulesTable L []))
            (setValues (V (.above 0)) (V (.above 1)) around))
          (exIntroByRules emptyOrPower (cPower cEmpty) emptyOrRightRule) Fin.elim0) ≠
      ev (chainHead V ground ν)
        (familyConsts base (tableLookup (rulesTable L []))
          (setValues (V (.above 0)) (V (.above 1)) around)) (cPower cEmpty) Fin.elim0 := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    reads_of_rulesTable fun _ declared => familyConsts_declared declared
  exact epsAsWitness_misses reads ν
    (setTheoryRules_setModel chain groundTyped aroundMem ν base)
    (emptyOrPower_typed setTheoryRules_over.sets) setTheoryRules_emptyOr_ex_empty
    setTheoryRules_emptyOr_ex_power (empty_ne_power chain groundTyped reads ν)

end ExistenceAgainstAPair

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
