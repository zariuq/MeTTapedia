import Mettapedia.SetTheory.OpenTower.ExternalTower
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation

/-!
# Hosting higher-order set theory and enclosing its model components

This constructs a set-stage interpretation and a host-relative consistency proof
for one exactly named derivation system: the retained higher-order proofs
(`ProofSyntax Symbol theory`) over the seven set laws of
`ZFSetHenkinInterpretation.theory` (extensionality, empty set, union, power set, separation and
replacement for every higher-order predicate and function, and set induction for every
predicate). These are the set laws of the HOTG profile.

**A stage is a model.** For a closed set containing `∅` (`Stage`), the standard higher-order
model whose sets are the members of the stage, with the actual set operations restricted to
it (`Stage.model`), validates all seven laws (`Stage.theory_valid`). Its higher-order
quantifiers range over every predicate and every function on the members of the stage.

**Every derivation is interpreted, and closed falsity is empty.** Each retained proof from the
seven laws has a section of its truth family in the stage model (`Stage.theoremSection`), and
the truth family of the closed formula `⊥` is empty (`Stage.falsity_empty`). Hence there is no
derivation of `⊥` from the seven laws (`Stage.consistent`). This is consistency of that exact
derivation system relative to the host; it is not an arithmetized consistency statement.

**Model components are enclosed in any later stage.** If the stage is a member of a closed
set `V`, then `V` contains a code for every higher-order type of the stage model (`code_mem`),
the codes of its six operations (`codedConstant_mem`), and, for every formula and coded
valuation, a truth fibre (`Stage.truthFibre_mem`). Lambda is a functional graph and
application reads its unique value, so terms are interpreted by set operations of the later
stage (`interpret`). The coded interpretation agrees with the stage model on every term
(`decode_interpret`). Every theorem has the inhabited fibre `{∅}` (`Stage.theorem_fibre`), and
closed falsity has the empty fibre (`Stage.falsity_fibre`), which gives another host-level
consistency proof (`Stage.consistent_from_internal_copy`). For each formula separately,
its extension is a coded predicate in the later stage. The theorem does not package the
whole interpretation as one internal set, encode satisfaction for all formulas, or prove
an internal arithmetized consistency statement; those require further syntax and
interpretation coding.

**The tower.** Every stage of the ω-tower is such a stage (`towerStage`), and each one's type
codes, operation codes and individual truth fibres belong to the next (`tower_hosting`). Along the
external tower, with no hypothesis, the image of a level is a stage one level up
(`imageStage`), and two levels up its lifted model components belong to the external stage
(`external_hosting`). A related external instance, from a whole level `ZFSet.{u}` into codes at
the next level, with the universe operation as an eleventh law under
`CofinalInaccessibles.{u}`, is `ZFSetHOLProofInterpretation` (`proofValue`,
`false_claim_has_no_proof`).

**Scope.** The derivation system is higher-order logic over set laws, not a dependent type
theory. A model whose equality is set equality validates more identity principles than an
intensional type theory requires; the next instance, a dependent fragment with Π, Σ, Id with
J and W, owes its own interpretation, coherence of substitution and identity profile.
Host choice is used by the replacement operation and by reading the value of a functional
graph.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Hosting

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetDependentProducts
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation
open ZFSetHOLTypeInterpretation (truthCode holds truth holds_truth truth_holds functionEquiv
  truthCode_mem)
open InternalTower ExternalTower ZFSetUniverseLift ZFSetLiftedUniverseClosure

universe u v

/-! ## Coded higher-order types over a carrier code -/

/-- The carrier of the base type: the members of a set. -/
abbrev Carrier (c : ZFSet.{u}) : Unit → Type (u + 1) := fun _ => Elements c

/-- Set codes of the higher-order types over the carrier code `c`: two truth values for
propositions, `c` for sets, and total functional graphs for arrows. -/
@[reducible] noncomputable def code (c : ZFSet.{u}) : Ty Unit → ZFSet.{u}
  | .prop => truthCode
  | .base _ => c
  | .arr A B => piSet (code c A) (fun _ => code c B)

/-- Every type code lies in every closed set that contains the carrier code. -/
theorem code_mem {V c : ZFSet.{u}} (hV : Closed V) (hc : c ∈ V) : ∀ A : Ty Unit, code c A ∈ V
  | .prop => truthCode_mem hV hc
  | .base _ => hc
  | .arr A B => hV.piSet_mem (code_mem hV hc A) _ (fun _ _ => code_mem hV hc B)

/-- The two truth-value codes are the propositions of the model. -/
noncomputable def truthDecode : Elements truthCode.{u} ≃ ULift.{u + 1} Prop where
  toFun value := .up (holds value)
  invFun value := truth value.down
  left_inv := truth_holds
  right_inv value := by
    apply ULift.ext
    exact propext (holds_truth value.down)

/-- Coded values are the values of the standard model over the members of `c`. -/
noncomputable def decode (c : ZFSet.{u}) :
    (A : Ty Unit) → Elements (code c A) ≃ Ty.denote.{0, u + 1} (Carrier c) A
  | .prop => truthDecode
  | .base _ => Equiv.refl _
  | .arr A B => (piEquiv (code c A) (fun _ => code c B)).trans
      (functionEquiv (decode c A) (decode c B))

/-! ## Graph lambda and application, and the coded interpretation of terms -/

section Coded

variable {c : ZFSet.{u}}

noncomputable def lam {A B : Ty Unit} (body : Elements (code c A) → Elements (code c B)) :
    Elements (code c (A ⇒ B)) :=
  encodeFunction (a := code c A) (b := fun _ => code c B) body

noncomputable def app {A B : Ty Unit} (function : Elements (code c (A ⇒ B)))
    (argument : Elements (code c A)) : Elements (code c B) :=
  graphValue (a := code c A) (b := fun _ => code c B) function argument

@[simp] theorem app_lam {A B : Ty Unit} (body : Elements (code c A) → Elements (code c B))
    (argument : Elements (code c A)) : app (lam body) argument = body argument :=
  congrFun (decode_encode_function (a := code c A) (b := fun _ => code c B) body) argument

theorem decode_app {A B : Ty Unit} (function : Elements (code c (A ⇒ B)))
    (argument : Elements (code c A)) :
    decode c B (app function argument) =
      decode c (A ⇒ B) function (decode c A argument) := by
  change decode c B (graphValue function argument) =
    decode c B (graphValue function ((decode c A).symm (decode c A argument)))
  rw [Equiv.symm_apply_apply]

theorem decode_lam {A B : Ty Unit} (body : Elements (code c A) → Elements (code c B)) :
    decode c (A ⇒ B) (lam body) = fun x => decode c B (body ((decode c A).symm x)) := by
  funext x
  change decode c B (app (lam body) ((decode c A).symm x)) = _
  rw [app_lam]

theorem decode_truth (p : Prop) : decode c .prop (truth p) = ULift.up p := by
  apply ULift.ext
  exact propext (holds_truth p)

/-- Valuations by coded values. -/
abbrev Valuation (c : ZFSet.{u}) (Γ : Ctx Unit) := ∀ {A}, Var Γ A → Elements (code c A)

def extend {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation c Γ) (x : Elements (code c A)) :
    Valuation c (A :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

noncomputable def decodeValuation {Γ : Ctx Unit} (ρ : Valuation c Γ) :
    ∀ {A}, Var Γ A → Ty.denote.{0, u + 1} (Carrier c) A :=
  fun {_} v => decode c _ (ρ v)

theorem decode_extend {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} (Carrier c) A)
    {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation c Γ) (x : Elements (code c A)) :
    (decodeValuation (extend ρ x) : ∀ {B}, Var (A :: Γ) B → Ty.denote.{0, u + 1} (Carrier c) B) =
      ((HenkinModel.standard (Carrier c) denotation).extend (decodeValuation ρ)
        (decode c A x) : ∀ {B}, Var (A :: Γ) B → Ty.denote.{0, u + 1} (Carrier c) B) := by
  funext B w
  cases w <;> rfl

/-- The coded interpretation: lambda builds a functional graph, application reads it, and the
quantifiers range over the members of the type codes. -/
noncomputable def interpret {Const : Ty Unit → Type v}
    (constants : {A : Ty Unit} → Const A → Elements (code c A)) :
    {Γ : Ctx Unit} → {A : Ty Unit} → Term Const Γ A → Valuation c Γ → Elements (code c A)
  | _, _, .var v, ρ => ρ v
  | _, _, .const k, _ => constants k
  | _, _, .app f x, ρ => app (interpret constants f ρ) (interpret constants x ρ)
  | _, _, .lam body, ρ => lam (fun x => interpret constants body (extend ρ x))
  | _, _, .top, _ => truth True
  | _, _, .bot, _ => truth False
  | _, _, .and p q, ρ => truth (holds (interpret constants p ρ) ∧ holds (interpret constants q ρ))
  | _, _, .or p q, ρ => truth (holds (interpret constants p ρ) ∨ holds (interpret constants q ρ))
  | _, _, .imp p q, ρ =>
      truth (holds (interpret constants p ρ) → holds (interpret constants q ρ))
  | _, _, .not p, ρ => truth (¬ holds (interpret constants p ρ))
  | _, _, .eq x y, ρ => truth (interpret constants x ρ = interpret constants y ρ)
  | _, _, .all p, ρ => truth (∀ x, holds (interpret constants p (extend ρ x)))
  | _, _, .ex p, ρ => truth (∃ x, holds (interpret constants p (extend ρ x)))

private theorem standard_eqv_of_eq {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} (Carrier c) A)
    {A : Ty Unit} {x y : Ty.denote.{0, u + 1} (Carrier c) A} (equal : x = y) :
    (HenkinModel.standard (Carrier c) denotation).Eqv A x y := by
  subst y
  exact (HenkinModel.standard (Carrier c) denotation).eqv_refl trivial

/-- **Coherence of the coded copy.** The coded interpretation of every term decodes to its
denotation in the standard model, provided the constants do. -/
theorem decode_interpret {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} (Carrier c) A)
    (constants : {A : Ty Unit} → Const A → Elements (code c A))
    (constant_law : ∀ {A} (k : Const A), decode c A (constants k) = denotation k)
    {Γ : Ctx Unit} {A : Ty Unit} (term : Term Const Γ A) (ρ : Valuation c Γ) :
    decode c A (interpret constants term ρ) =
      (HenkinModel.standard (Carrier c) denotation).denote term (decodeValuation ρ) := by
  induction term with
  | var => rfl
  | const k => exact constant_law k
  | app f x ihf ihx =>
      rw [interpret, decode_app, ihf, ihx]
      rfl
  | lam body ih =>
      rw [interpret, decode_lam]
      funext x
      rw [ih, decode_extend, Equiv.apply_symm_apply]
      rfl
  | top => exact decode_truth True
  | bot => exact decode_truth False
  | and p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((decode c .prop (interpret constants p ρ)).down ∧
        (decode c .prop (interpret constants q ρ)).down) = _
      rw [ihp, ihq]
      rfl
  | or p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((decode c .prop (interpret constants p ρ)).down ∨
        (decode c .prop (interpret constants q ρ)).down) = _
      rw [ihp, ihq]
      rfl
  | imp p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((decode c .prop (interpret constants p ρ)).down →
        (decode c .prop (interpret constants q ρ)).down) = _
      rw [ihp, ihq]
      rfl
  | not p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change (¬ (decode c .prop (interpret constants p ρ)).down) = _
      rw [ih]
      rfl
  | eq x y ihx ihy =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change interpret constants x ρ = interpret constants y ρ ↔
        (HenkinModel.standard (Carrier c) denotation).Eqv _ _ _
      constructor
      · intro equal
        have valueEqual := congrArg (decode c _) equal
        rw [ihx, ihy] at valueEqual
        exact standard_eqv_of_eq denotation valueEqual
      · intro equal
        apply (decode c _).injective
        rw [ihx, ihy]
        exact (HenkinModel.standard (Carrier c) denotation).eq_of_eqv_of_fullDomains
          (HenkinModel.fullDomains_standard (Carrier c) denotation) equal
  | @all A Γ p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∀ x, (decode c .prop (interpret constants p (extend ρ x))).down) ↔
        ∀ x, True → _
      simp only [ih, decode_extend denotation]
      constructor
      · intro hp x _
        have hx := hp ((decode c A).symm x)
        exact Eq.mp (congrArg (fun y : Ty.denote.{0, u + 1} (Carrier c) A =>
          ((HenkinModel.standard (Carrier c) denotation).denote p
            ((HenkinModel.standard (Carrier c) denotation).extend (decodeValuation ρ) y)).down)
          (Equiv.apply_symm_apply (decode c A) x)) hx
      · intro hp x
        exact hp (decode c A x) trivial
  | @ex A Γ p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∃ x, (decode c .prop (interpret constants p (extend ρ x))).down) ↔
        ∃ x, True ∧ _
      simp only [ih, decode_extend denotation]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨decode c A x, trivial, hx⟩
      · rintro ⟨x, _, hx⟩
        refine ⟨(decode c A).symm x, ?_⟩
        exact Eq.mpr (congrArg (fun y : Ty.denote.{0, u + 1} (Carrier c) A =>
          ((HenkinModel.standard (Carrier c) denotation).denote p
            ((HenkinModel.standard (Carrier c) denotation).extend (decodeValuation ρ) y)).down)
          (Equiv.apply_symm_apply (decode c A) x)) hx

def emptyValuation : Valuation c [] := fun {_} boundVar => nomatch boundVar

end Coded

/-! ## A stage as a model of the seven set laws -/

/-- A stage: a closed set containing the empty set. -/
structure Stage : Type (u + 1) where
  carrier : ZFSet.{u}
  closed : Closed carrier
  empty_mem : (∅ : ZFSet.{u}) ∈ carrier

namespace Stage

variable (S : Stage.{u})

/-- Extend a function on the members of the stage to all sets. -/
noncomputable def extendMap (f : Elements S.carrier → Elements S.carrier) (x : ZFSet.{u}) :
    ZFSet.{u} := by
  classical
  exact if hx : x ∈ S.carrier then (f ⟨x, hx⟩).1 else ∅

theorem extendMap_of_mem (f : Elements S.carrier → Elements S.carrier) {x : ZFSet.{u}}
    (hx : x ∈ S.carrier) : S.extendMap f x = (f ⟨x, hx⟩).1 := by
  simp only [extendMap, dif_pos hx]

/-- The six set operations, restricted to the members of the stage. -/
noncomputable def denoteSymbol :
    {A : Ty Unit} → Symbol A → Ty.denote.{0, u + 1} (Carrier S.carrier) A
  | _, .member => fun (x a : Elements S.carrier) => .up (x.1 ∈ a.1)
  | _, .empty => (⟨∅, S.empty_mem⟩ : Elements S.carrier)
  | _, .union => fun (a : Elements S.carrier) =>
      (⟨ZFSet.sUnion a.1, S.closed.union_mem a.2⟩ : Elements S.carrier)
  | _, .power => fun (a : Elements S.carrier) =>
      (⟨ZFSet.powerset a.1, S.closed.power_mem a.2⟩ : Elements S.carrier)
  | _, .separate => fun (a : Elements S.carrier) p =>
      (⟨ZFSet.sep (fun x => ∃ hx : x ∈ S.carrier, (p ⟨x, hx⟩).down) a.1,
        S.closed.separation_mem a.2 _⟩ : Elements S.carrier)
  | _, .replace => fun (a : Elements S.carrier) (f : Elements S.carrier → Elements S.carrier) =>
      (⟨replacement a.1 (S.extendMap f), S.closed.replacement_mem a.2 _ (fun x hx => by
        rw [S.extendMap_of_mem f (S.closed.transitive _ a.2 hx)]
        exact (f _).2)⟩ : Elements S.carrier)

/-- The standard higher-order model over the members of the stage. -/
noncomputable def model : HenkinModel.{0, 0, u + 1} Unit Symbol :=
  HenkinModel.standard (Carrier S.carrier) S.denoteSymbol

theorem extensionality_valid : S.model.models extensionality := by
  intro a _ b _ h
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (h ⟨z, S.closed.transitive _ a.2 hz⟩ trivial).1 hz
  · intro hz
    exact (h ⟨z, S.closed.transitive _ b.2 hz⟩ trivial).2 hz

theorem emptyLaw_valid : S.model.models emptyLaw := by
  intro x _
  exact ZFSet.notMem_empty x.1

theorem unionLaw_valid : S.model.models unionLaw := by
  intro a _ x _
  constructor
  · intro h
    obtain ⟨y, hya, hxy⟩ := ZFSet.mem_sUnion.mp h
    exact ⟨⟨y, S.closed.transitive _ a.2 hya⟩, trivial, hya, hxy⟩
  · rintro ⟨y, _, hya, hxy⟩
    exact ZFSet.mem_sUnion.mpr ⟨y.1, hya, hxy⟩

theorem powerLaw_valid : S.model.models powerLaw := by
  intro a _ b _
  constructor
  · intro h x _ hx
    exact ZFSet.mem_powerset.mp h hx
  · intro h
    exact ZFSet.mem_powerset.mpr (fun z hz => h ⟨z, S.closed.transitive _ b.2 hz⟩ trivial hz)

theorem separationLaw_valid : S.model.models separationLaw := by
  intro a _ p _ x _
  change Elements S.carrier at a x
  change Elements S.carrier → ULift.{u + 1} Prop at p
  change (x.1 ∈ ZFSet.sep (fun y => ∃ hy : y ∈ S.carrier, (p ⟨y, hy⟩).down) a.1 →
      x.1 ∈ a.1 ∧ (p x).down) ∧
    (x.1 ∈ a.1 ∧ (p x).down →
      x.1 ∈ ZFSet.sep (fun y => ∃ hy : y ∈ S.carrier, (p ⟨y, hy⟩).down) a.1)
  constructor
  · intro h
    obtain ⟨hxa, _, hp⟩ := ZFSet.mem_sep.mp h
    exact ⟨hxa, hp⟩
  · rintro ⟨hxa, hp⟩
    exact ZFSet.mem_sep.mpr ⟨hxa, x.2, hp⟩

theorem replacementLaw_valid : S.model.models replacementLaw := by
  intro a _ f _ y _
  change Elements S.carrier at a y
  change Elements S.carrier → Elements S.carrier at f
  change (y.1 ∈ replacement a.1 (S.extendMap f) →
      ∃ x : Elements S.carrier, True ∧ x.1 ∈ a.1 ∧ f x = y) ∧
    ((∃ x : Elements S.carrier, True ∧ x.1 ∈ a.1 ∧ f x = y) →
      y.1 ∈ replacement a.1 (S.extendMap f))
  constructor
  · intro h
    obtain ⟨x, hxa, hxy⟩ := mem_replacement.mp h
    have hx : x ∈ S.carrier := S.closed.transitive _ a.2 hxa
    refine ⟨⟨x, hx⟩, trivial, hxa, ?_⟩
    apply Subtype.ext
    rw [← hxy, S.extendMap_of_mem f hx]
  · rintro ⟨x, _, hxa, hxy⟩
    refine mem_replacement.mpr ⟨x.1, hxa, ?_⟩
    rw [S.extendMap_of_mem f x.2]
    exact congrArg Subtype.val hxy

theorem setInduction_valid : S.model.models setInduction := by
  intro p _ step x _
  have key : ∀ z : ZFSet.{u}, ∀ hz : z ∈ S.carrier, (p ⟨z, hz⟩).down := by
    intro z
    induction z using ZFSet.inductionOn with
    | h z ih =>
      intro hz
      exact step ⟨z, hz⟩ trivial (fun b _ hbz => ih b.1 hbz b.2)
  exact key x.1 x.2

/-- **A stage is a model of the seven set laws.** -/
theorem theory_valid (φ : ClosedFormula Symbol) (h : φ ∈ theory) : S.model.models φ := by
  simp only [theory, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S.extensionality_valid
  · exact S.emptyLaw_valid
  · exact S.unionLaw_valid
  · exact S.powerLaw_valid
  · exact S.separationLaw_valid
  · exact S.replacementLaw_valid
  · exact S.setInduction_valid

theorem fullDomains : S.model.FullDomains :=
  HenkinModel.fullDomains_standard (Carrier S.carrier) S.denoteSymbol

theorem functionsRespectEqv : S.model.FunctionsRespectEqv :=
  S.model.functionsRespectEqv_of_fullDomains S.fullDomains

/-- The empty context, read as the decoding of the empty coded valuation. -/
noncomputable def emptyContext : AdmissibleContext S.model [] :=
  ⟨decodeValuation (c := S.carrier) emptyValuation, by intro A v; exact nomatch v⟩

noncomputable def satisfiedTheory : SatisfiedContext S.model theory :=
  ⟨S.emptyContext, by
    intro φ memberTheory
    refine Eq.mp ?_ (S.theory_valid φ memberTheory)
    unfold HenkinModel.models PreModel.models
    congr 2
    funext A v
    nomatch v⟩

/-- **Every derivation is interpreted:** a proof from the seven laws is a section of its
truth family in the stage model. -/
noncomputable def theoremSection {φ : ClosedFormula Symbol}
    (proof : ProofSyntax Symbol theory φ) : truthFamily S.model φ S.emptyContext :=
  proofSection S.model S.functionsRespectEqv proof S.satisfiedTheory

/-- **Closed falsity has an empty interpretation.** -/
theorem falsity_empty :
    IsEmpty (truthFamily S.model (.bot : ClosedFormula Symbol) S.emptyContext) :=
  ⟨fun witness => witness.down.down⟩

/-- **Consistency of the derivation system, relative to the host.** -/
theorem consistent (S : Stage.{u}) : ¬ Nonempty (ProofSyntax Symbol theory .bot) := by
  rintro ⟨proof⟩
  exact (S.theoremSection proof).down.down

/-! ## The stage model inside a later stage -/

/-- The six operations of the stage, as coded values. -/
noncomputable def codedConstants {A : Ty Unit} (k : Symbol A) : Elements (code S.carrier A) :=
  (decode S.carrier A).symm (S.denoteSymbol k)

theorem decode_codedConstants {A : Ty Unit} (k : Symbol A) :
    decode S.carrier A (S.codedConstants k) = S.denoteSymbol k :=
  Equiv.apply_symm_apply _ _

/-- The coded interpretation agrees with the stage model on every term. -/
theorem decode_interpret_stage {Γ : Ctx Unit} {A : Ty Unit} (t : Term Symbol Γ A)
    (ρ : Valuation S.carrier Γ) :
    decode S.carrier A (interpret S.codedConstants t ρ) =
      S.model.denote t (decodeValuation ρ) :=
  decode_interpret S.denoteSymbol S.codedConstants S.decode_codedConstants t ρ

/-- The truth fibre of a formula at a coded valuation: `{∅}` when it holds, `∅` otherwise. -/
noncomputable def truthFibre {Γ : Ctx Unit} (φ : Formula Symbol Γ)
    (ρ : Valuation S.carrier Γ) : ZFSet.{u} :=
  ZFSet.sep (fun _ => holds (interpret S.codedConstants φ ρ)) {∅}

theorem mem_truthFibre {Γ : Ctx Unit} (φ : Formula Symbol Γ) (ρ : Valuation S.carrier Γ)
    (x : ZFSet.{u}) :
    x ∈ S.truthFibre φ ρ ↔ x = ∅ ∧ holds (interpret S.codedConstants φ ρ) := by
  simp only [truthFibre, ZFSet.mem_sep, ZFSet.mem_singleton]

theorem holds_iff_model {Γ : Ctx Unit} (φ : Formula Symbol Γ) (ρ : Valuation S.carrier Γ) :
    holds (interpret S.codedConstants φ ρ) ↔ (S.model.denote φ (decodeValuation ρ)).down := by
  have agreement := congrArg ULift.down (S.decode_interpret_stage φ ρ)
  exact Iff.of_eq agreement

/-- Every theorem of the seven laws has the inhabited truth fibre. -/
theorem theorem_fibre {φ : ClosedFormula Symbol} (proof : ProofSyntax Symbol theory φ) :
    (∅ : ZFSet.{u}) ∈ S.truthFibre φ emptyValuation := by
  exact (S.mem_truthFibre φ emptyValuation ∅).mpr
    ⟨rfl, (S.holds_iff_model φ _).mpr (S.theoremSection proof).down.down⟩

/-- **Closed falsity has the empty fibre**, at every coded valuation. -/
theorem falsity_fibre {Γ : Ctx Unit} (ρ : Valuation S.carrier Γ) :
    S.truthFibre (.bot : Formula Symbol Γ) ρ = ∅ := by
  apply ZFSet.ext
  intro x
  rw [S.mem_truthFibre]
  simp only [interpret, holds_truth, and_false, ZFSet.notMem_empty]

/-- Host-relative consistency using the coded truth fibres: a proof of falsity would put
`∅` in the empty fibre. This conclusion is external and has no later-stage parameter. -/
theorem consistent_from_internal_copy (S : Stage.{u}) :
    ¬ Nonempty (ProofSyntax Symbol theory .bot) := by
  rintro ⟨proof⟩
  have member := S.theorem_fibre proof
  rw [S.falsity_fibre] at member
  exact ZFSet.notMem_empty _ member

theorem truthFibre_mem {V : ZFSet.{u}} (hV : Closed V) (hS : S.carrier ∈ V) {Γ : Ctx Unit}
    (φ : Formula Symbol Γ) (ρ : Valuation S.carrier Γ) : S.truthFibre φ ρ ∈ V :=
  hV.subset_mem (hV.singleton_mem (hV.empty_mem hS)) ZFSet.sep_subset

theorem codedConstant_mem {V : ZFSet.{u}} (hV : Closed V) (hS : S.carrier ∈ V) {A : Ty Unit}
    (k : Symbol A) : (S.codedConstants k).1 ∈ V :=
  hV.transitive _ (code_mem hV hS A) (S.codedConstants k).2

/-- Each type code, operation code and individual truth fibre belongs to the later closed
set, and the coded interpretation agrees with the stage model on every term. This is
componentwise enclosure, not a single internal code for the whole interpretation. -/
theorem internal_copy {V : ZFSet.{u}} (hV : Closed V) (hS : S.carrier ∈ V) :
    (∀ A : Ty Unit, code S.carrier A ∈ V) ∧
      (∀ {A : Ty Unit} (k : Symbol A), (S.codedConstants k).1 ∈ V) ∧
      (∀ {Γ : Ctx Unit} (φ : Formula Symbol Γ) (ρ : Valuation S.carrier Γ),
        S.truthFibre φ ρ ∈ V) ∧
      (∀ {Γ : Ctx Unit} {A : Ty Unit} (t : Term Symbol Γ A) (ρ : Valuation S.carrier Γ),
        decode S.carrier A (interpret S.codedConstants t ρ) =
          S.model.denote t (decodeValuation ρ)) :=
  ⟨code_mem hV hS, fun k => S.codedConstant_mem hV hS k,
    fun φ ρ => S.truthFibre_mem hV hS φ ρ, fun t ρ => S.decode_interpret_stage t ρ⟩

end Stage

/-! ## Hosting along the ω-tower -/

/-- Each stage of the ω-tower, as a stage. -/
noncomputable def towerStage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    Stage.{u} :=
  ⟨stage h N n, stage_closed h N n, empty_mem_stage h N n⟩

/-- Stage `n` models the seven set laws with every derivation interpreted and falsity empty.
Its type codes, operation codes and individual truth fibres belong to stage `n + 1`. -/
theorem tower_hosting (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    (∀ φ ∈ theory, (towerStage h N n).model.models φ) ∧
      IsEmpty (truthFamily (towerStage h N n).model (.bot : ClosedFormula Symbol)
        (towerStage h N n).emptyContext) ∧
      (∀ A : Ty Unit, code (stage h N n) A ∈ stage h N (n + 1)) ∧
      (∀ {A : Ty Unit} (k : Symbol A), ((towerStage h N n).codedConstants k).1 ∈
        stage h N (n + 1)) ∧
      (∀ {Γ : Ctx Unit} (φ : Formula Symbol Γ) (ρ : Valuation (stage h N n) Γ),
        (towerStage h N n).truthFibre φ ρ ∈ stage h N (n + 1)) := by
  obtain ⟨codes, constants, fibres, _⟩ :=
    (towerStage h N n).internal_copy (stage_closed h N (n + 1)) (stage_mem_succ h N n)
  exact ⟨(towerStage h N n).theory_valid, (towerStage h N n).falsity_empty, codes, constants,
    fibres⟩

/-! ## Hosting along the external tower, without hypotheses -/

/-- The image of a whole level, one level up, as a stage. -/
noncomputable def imageStage : Stage.{u + 1} :=
  ⟨carrierCode.{u}, carrierCode_closed, carrierCode_closed.empty_mem omega_mem_image⟩

/-- The same stage, lifted one more level. -/
noncomputable def liftedImageStage : Stage.{u + 2} :=
  ⟨lift carrierCode.{u}, closed_lift carrierCode_closed, by
    rw [← lift_empty]
    exact lift_mem_lift.mpr imageStage.empty_mem⟩

/-- The image of level `u` models the seven set laws, with falsity empty, at level `u + 1`,
without an inaccessible hypothesis. Two levels up, its lifted type codes, operation codes
and individual truth fibres belong to the external stage `carrierCode.{u+1}`. -/
theorem external_hosting :
    (∀ φ ∈ theory, imageStage.{u}.model.models φ) ∧
      IsEmpty (truthFamily imageStage.{u}.model (.bot : ClosedFormula Symbol)
        imageStage.emptyContext) ∧
      (∀ A : Ty Unit, code (lift carrierCode.{u}) A ∈ carrierCode.{u + 1}) ∧
      (∀ {A : Ty Unit} (k : Symbol A), (liftedImageStage.{u}.codedConstants k).1 ∈
        carrierCode.{u + 1}) ∧
      (∀ {Γ : Ctx Unit} (φ : Formula Symbol Γ) (ρ : Valuation (lift carrierCode.{u}) Γ),
        liftedImageStage.{u}.truthFibre φ ρ ∈ carrierCode.{u + 1}) := by
  obtain ⟨codes, constants, fibres, _⟩ :=
    liftedImageStage.{u}.internal_copy carrierCode_closed
      (mem_carrierCode.mpr ⟨carrierCode.{u}, rfl⟩)
  exact ⟨imageStage.theory_valid, imageStage.falsity_empty, codes, constants, fibres⟩

#print axioms decode_interpret
#print axioms Stage.theory_valid
#print axioms Stage.theoremSection
#print axioms Stage.falsity_empty
#print axioms Stage.consistent
#print axioms Stage.theorem_fibre
#print axioms Stage.falsity_fibre
#print axioms Stage.consistent_from_internal_copy
#print axioms Stage.internal_copy
#print axioms tower_hosting
#print axioms external_hosting

end Mettapedia.SetTheory.OpenTower.Hosting
