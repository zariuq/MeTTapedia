import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormFactsBridge
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchConstantControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchFormsControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchFundamentalControls

/-!
# Controls for the adequacy of every constant of the object package

**Positive: the recursor computes, read off the relation** (`recZeroOne_reduces_suc`).
`num-rec (λ _. num) 1 (λ m h. suc h) 0` is typed at `(λ _. num) 0`, and the successor tag
is a typed token of its denotation. The adequacy of every constant makes the typing valid,
and the relation at that token says the term reduces, typed, to a successor.

**Positive: an implication of closed codes decodes to a dependent function type**
(`impZero_decodes_pi`). The dependent-function tag is a typed token of the denotation of
`(0 = 0) → (0 = 0)`; the relation at that token, through the clause of the codes, says the
decoder applied to the code reduces to a dependent function type.

**Negative: implication read as the code of the numbers** (`natImpReading_not_constAdequate`).
Under the reading that sends two codes to the code of the numbers, implication is not
adequate, although its declared type stays adequate (`natImpReading_adequateType`): the
reading's token says the decoding of an implication reduces to the numbers, while it
reduces to a dependent function type, a different normal form.

**Positive and negative: the recursor needs the step at its numeral.** Under the object
package's weak-head reduction, the adequacy of every constant makes
`num-rec (λ _. num) 1 (λ m h. suc h) ((λ x. x) 0)` reduce to a successor
(`recStuck_reduces_suc`): its numeral reduces first, by the step at the recursor's numeral.
Under the core reduction, which has no step at an inspected argument, the term takes no
step (`recStuck_normal`); `num`, `zero` and `suc` stay adequate, and the recursor is not
adequate (`numRec_not_constAdequate_core`).

**The ground types.** A token of the numbers is typed at them (`typedAt_natI_zero`), while
no token is typed at the sets (`not_typedAt_groundI`).

**The erasure of matching forms.** Equal annotated dependent function types over the
numbers match; their erasures match as raw types (`formsMatch_piNumNum_erase`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypedAt principal natI zeroI succI
  codesIdeal)
open Package (numRecName)

namespace CodeModel
namespace AdequacyControls

open ConstantControls (tyTok_lamEntry below_piEntry ent_nil_lam1 ty_nil)

/-! ## Positive: the recursor computes, read off the relation -/

section Recursor

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The motive `λ (_ : num). num`. -/
abbrev motiveNum {n : Nat} : CTm Tower.Head n := .lam cnum cnum

/-- The numeral one. -/
abbrev cOne {n : Nat} : CTm Tower.Head n := csuc czero

/-- The step `λ (m : num) (h : P m). suc h`, annotated at the motive. -/
abbrev sucStepAt {n : Nat} : CTm Tower.Head n :=
  .lam cnum (.lam (.app motiveNum (.var 0)) (csuc (.var 0)))

/-- `num-rec (λ _. num) 1 (λ m h. suc h) 0`. -/
abbrev recZeroOne : CTm Tower.Head 0 := cRecApp motiveNum cOne sucStepAt czero

theorem motiveNum_typed : CTyped objectChurch Γ motiveNum (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _) cnum_typed

/-- The motive at a number is the numbers, by β. -/
theorem motiveNum_beta {a : CTm Tower.Head n} (ta : CTyped objectChurch Γ a cnum) :
    CEqual objectChurch Γ (.app motiveNum a) cnum cU0 :=
  CDerivable.betaPi (cpiT (craise cnum_typed) cU0_typed) (.sort _) cnum_typed ta

theorem cOne_typed_motive : CTyped objectChurch Γ cOne (.app motiveNum czero) :=
  .conv (csuc_typed czero_typed) (.symm (motiveNum_beta czero_typed)) (.sort _)

theorem sucStepAt_typed :
    CTyped objectChurch Γ sucStepAt
      (.pi cnum (.pi (.app motiveNum (.var 0)) (.app motiveNum (csuc (.var 1))))) := by
  have tPx : CTyped objectChurch (.snoc Γ cnum) (.app motiveNum (.var 0)) cU0 :=
    .appElim (B := cU0) motiveNum_typed (.var 0)
  have h : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app motiveNum (.var 0))) (.var 0) cnum :=
    .conv (.var 0) (motiveNum_beta (.var 1)) (.sort _)
  have body : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app motiveNum (.var 0)))
      (csuc (.var 0)) (.app motiveNum (csuc (.var 1))) :=
    .conv (csuc_typed h) (.symm (motiveNum_beta (csuc_typed (.var 1)))) (.sort _)
  have tPi₂ : CTyped objectChurch (.snoc Γ cnum)
      (.pi (.app motiveNum (.var 0)) (.app motiveNum (csuc (.var 1)))) cU0 :=
    cpiT tPx (.appElim (B := cU0) motiveNum_typed (csuc_typed (.var 1)))
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed tPi₂) (.sort _)
    (.lamIntro tPx (.sort _) tPi₂ (.sort _) body)

theorem recZeroOne_typed : CTyped objectChurch .nil recZeroOne (.app motiveNum czero) := by
  have r1 := CDerivable.appElim (cnumRec_typed (Γ := .nil)) motiveNum_typed
  have r2 := CDerivable.appElim r1 cOne_typed_motive
  have r3 := CDerivable.appElim r2 sucStepAt_typed
  exact CDerivable.appElim r3 czero_typed

/-- The recursion is its zero case, `1`, by the zero rule. -/
theorem recZeroOne_equal : CEqual objectChurch .nil recZeroOne cOne (.app motiveNum czero) :=
  objectRootAdmitted .nil (cnumRecZero_step motiveNum cOne sucStepAt) recZeroOne_typed

/-- The successor tag is a token of the recursion's denotation. -/
theorem recZeroOne_mem_succ :
    (cinterp objectChurchReading recZeroOne Env.nil).Mem (.tag .succ) := by
  rw [objectChurch_soundnessFacts.equality recZeroOne_equal Env.nil trivial]
  change (Ideal.app (objectChurchReading.const sucN) (objectChurchReading.const zeroN)).Mem _
  rw [objectChurchReading_suc, app_sucConst objectChurchReading numNames objectChurchReading_num]
  exact Ideal.succI_mem_succ _

/-- The successor tag is typed at the recursion's type, the motive at zero. -/
theorem typedAt_motiveZero_succ :
    TypedAt (cinterp objectChurchReading (.app motiveNum czero : CTm Tower.Head 0) Env.nil)
      (.tag .succ) := by
  change TypedAt (Ideal.app (Ideal.clam (objectChurchReading.const numN)
    fun _ => objectChurchReading.const numN) (objectChurchReading.const zeroN)) _
  rw [Ideal.app_clam (Ideal.Cont.const _), objectChurchReading_num]
  exact ⟨Elem.nat, Ideal.below_nat, Ideal.nat_type, tyTok_tag_succ.2 List.mem_cons_self⟩

/-- **The recursor computes, read off the relation**: the adequacy of every constant makes
the typing of `num-rec (λ _. num) 1 (λ m h. suc h) 0` valid, and the relation at the
successor tag of its denotation says it reduces, typed, to a successor. -/
theorem recZeroOne_reduces_suc :
    ∃ m, CRedTm objectHeadReduction .nil recZeroOne (csuc m) (.app motiveNum czero) := by
  have valid := objectChurch_fundamental recZeroOne_typed CCtxFormed.nil
  have rel := valid.1 Env.nil trivial CCtxFormed.nil SubstRel.nil (.tag .succ) recZeroOne_mem_succ
    typedAt_motiveZero_succ
  obtain ⟨m, -, -, red, -, -⟩ := RT.tm_succTag_iff.1 rel
  exact ⟨m, red⟩

end Recursor

/-! ## Positive: an implication of closed codes decodes to a dependent function type -/

section Implication

/-- The closed code `0 = 0`, at the numbers. -/
abbrev cZeroEq : CTm Tower.Head 0 :=
  .app (.app (.const (SetProfile.eqName SetProfile.numTy)) czero) czero

/-- The closed code `(0 = 0) → (0 = 0)`. -/
abbrev cImpZero : CTm Tower.Head 0 := .app (.app (.const impN) cZeroEq) cZeroEq

theorem cZeroEq_typed : CTyped objectChurch .nil cZeroEq (.const propN) :=
  CDerivable.appElim (A := cnum) (B := .const propN)
    (CDerivable.appElim (A := cnum) (B := .pi cnum (.const propN))
      (ceq_typed SetProfile.numTy (Γ := .nil)) czero_typed) czero_typed

theorem cImpZero_typed : CTyped objectChurch .nil cImpZero (.const propN) :=
  CDerivable.appElim (A := .const propN) (B := .const propN)
    (CDerivable.appElim (A := .const propN) (B := .pi (.const propN) (.const propN)) cimp_typed
      cZeroEq_typed) cZeroEq_typed

/-- The dependent-function tag is typed at the codes. -/
theorem typedAt_codes_piTag : TypedAt codesIdeal (.tag .pi) :=
  Ideal.typedAt_codes_iff.2 ((tyTok_tag_former (k := .pi) trivial).2 Elem.isUniv_univ)

/-- The dependent-function tag is a token of the implication's denotation. -/
theorem cImpZero_mem_pi : (cinterp objectChurchReading cImpZero Env.nil).Mem (.tag .pi) := by
  change (Ideal.appSpine (objectChurchReading.const impN)
    [cinterp objectChurchReading cZeroEq Env.nil, cinterp objectChurchReading cZeroEq Env.nil]).Mem _
  rw [objectChurchReading_imp, Ideal.appSpine_impConst]
  exact Ideal.subset_closure ⟨Ideal.mem_former_tag _ _ _, typedAt_codes_piTag⟩

/-- **An implication of closed codes decodes to a dependent function type**, read off the
relation at the dependent-function tag of the implication's denotation. -/
theorem impZero_decodes_pi :
    ∃ D E, CRedTy objectHeadReduction .nil (.app (.const holdsN) cImpZero) (.pi D E) := by
  have valid := objectChurch_fundamental cImpZero_typed CCtxFormed.nil
  have rel := valid.1 Env.nil trivial CCtxFormed.nil SubstRel.nil (.tag .pi) cImpZero_mem_pi
    (by rw [cinterp_propT]; exact typedAt_codes_piTag)
  have codes := RT.toCodes rfl (propRed objectExtension) rel
  obtain ⟨D, E, -, -, red, -⟩ := RT.ty_pi_iff.1 codes
  exact ⟨D, E, red⟩

end Implication

/-! ## Negative: implication read as the code of the numbers -/

section NatImplication

/-- The annotated declared type of implication, `prop → prop → prop`. -/
abbrev impDecl : CTm Tower.Head 0 := .pi (.const propN) (.pi (.const propN) (.const propN))

/-- The reading that sends two codes to the code of the numbers, and reads every other
constant as the object reading does. -/
def natImpReading : Reading Tower.Head :=
  ⟨objectHead, fun c => if c = impN then
    projT (cinterp objectChurchReading impDecl Env.nil) (Ideal.lam fun _ => Ideal.lam fun _ => natI)
    else objectChurchReading.const c⟩

theorem natImpReading_imp : natImpReading.const impN =
    projT (cinterp objectChurchReading impDecl Env.nil)
      (Ideal.lam fun _ => Ideal.lam fun _ => natI) := by
  show (if impN = impN then _ else objectChurchReading.const impN) = _
  exact if_pos rfl

/-- The reading reads every constant other than implication as the object reading does. -/
theorem natImpReading_const_ne {c : DeclName} (h : c ≠ impN) :
    natImpReading.const c = objectChurchReading.const c :=
  if_neg h

/-- The reading interprets the declared type of implication as the object reading does. -/
theorem natImpReading_cinterp_impDecl {ρ : Env 0} :
    cinterp natImpReading impDecl ρ = cinterp objectChurchReading impDecl Env.nil := by
  rw [Env.eq_nil ρ Env.nil]
  refine congrFun (cinterp_congr (Rd := natImpReading) (Rd' := objectChurchReading) rfl _
    fun c hc => ?_) Env.nil
  have hc' : c = propN := by
    simp only [termConsts, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, or_self] at hc
    exact hc
  rw [hc']
  exact natImpReading_const_ne (by decide)

/-- **The declared type of implication stays adequate under the reading.** -/
theorem natImpReading_adequateType :
    AdequateType natImpReading objectHeadReduction .nil impDecl := by
  intro ρ _ m Δ σ σ' formed hσ r hr hrU
  rw [natImpReading_cinterp_impDecl] at hr
  exact adequateType_typeAt objectExtension (H := objectHeadReduction) (.arr .prop (.arr .prop .prop)) .nil
    Env.nil trivial formed ⟨hσ.1, fun i => i.elim0⟩ r hr hrU

/-- The reading's token: at any two codes, the tag of the numbers. -/
def natTok : Tok := .fn .lam [] [] [.fn .lam [] [] [.tag .nat]]

/-- The compact type witness of the token. -/
def natTokWitness : List Tok := Elem.former .pi [] [([], Elem.former .pi [] [([], Elem.codes)])]

theorem ty_codes : Ty Elem.codes Elem.univ := fun t ht => by
  rw [List.mem_singleton.1 ht]
  exact (tyTok_tag_former (k := .codes) trivial).2 Elem.isUniv_univ

theorem ty_natTokWitness : Ty natTokWitness Elem.univ := by
  have entry : ∀ {W : List Tok}, Ty W Elem.univ →
      Ty (Elem.former .pi [] [([], W)]) Elem.univ := fun hW =>
    Elem.ty_former (.inl rfl) Elem.isUniv_univ (ty_nil _) fun p hp => by
      rw [List.mem_singleton.1 hp]
      exact ⟨ty_nil _, hW⟩
  exact entry (entry ty_codes)

theorem tyTok_natTok : TyTok natTokWitness natTok :=
  tyTok_lamEntry (ty_nil _) (tyTok_lamEntry (ty_nil _)
    ((tyTok_tag_former (k := .nat) trivial).2 (.inr List.mem_cons_self)))

theorem below_natTokWitness :
    Ideal.Below natTokWitness (cinterp objectChurchReading impDecl Env.nil) :=
  below_piEntry (fun _ h => absurd h List.not_mem_nil)
    (below_piEntry (fun _ h => absurd h List.not_mem_nil) fun t ht => by
      rw [List.mem_singleton.1 ht, cinterp_propT]
      exact ent_of_mem List.mem_cons_self)

theorem typedAt_natTok : TypedAt (cinterp objectChurchReading impDecl Env.nil) natTok :=
  ⟨natTokWitness, below_natTokWitness, ty_natTokWitness, tyTok_natTok⟩

theorem natImpReading_mem_natTok : (natImpReading.const impN).Mem natTok := by
  rw [natImpReading_imp]
  refine Ideal.subset_closure ⟨?_, typedAt_natTok⟩
  refine (Ideal.mem_lam_fn fun _ => Ideal.le_refl _).2 fun y hy => ?_
  rw [List.mem_singleton.1 hy]
  refine (Ideal.mem_lam_fn fun _ => Ideal.le_refl _).2 fun z hz => ?_
  rw [List.mem_singleton.1 hz]
  exact ent_of_mem List.mem_cons_self

/-- The decoding of an implication of the two code variables reduces to its dependent
function type. -/
theorem impVars_decode_red :
    CRedTy objectHeadReduction cImpTele
      (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0))) cImpDecoding :=
  ⟨.single (objectHeadReduction.root (objectChurch_decodeImp (.var 1) (.var 0))), _, .sort _,
    .rootAdmitted (objectChurch_decodeImp (.var 1) (.var 0))
      (objectChurch_decodeImp_admits (.var 1) (.var 0)) (holds_app_typed cimpSpine_typed)
      (.sub (.piForm (holds_app_typed (.var 1)) (.sort _) (holds_app_typed (.var 1)) (.sort _)
        (.sorts _ _)) (.subUniv cumulative_max_zero))⟩

theorem cImpTele_formed : CCtxFormed objectChurch cImpTele :=
  .snoc (.snoc .nil ⟨_, .sort _, const_U0_typed (by decide)⟩) ⟨_, .sort _, const_U0_typed (by decide)⟩

/-- **Implication is not adequate under the reading of two codes as the code of the
numbers.** At the reading's token, adequacy would relate the implication of the two code
variables to itself at the tag of the numbers, through the clause of the codes: its
decoding would reduce to the numbers. It reduces to a dependent function type, a different
normal form. -/
theorem natImpReading_not_constAdequate : ¬ ConstAdequateAt natImpReading objectHeadReduction impN := by
  intro h
  have declared : objectChurch.constantType impN = some impDecl :=
    objectChurch_declared (T := programCodes.impType) (by decide) rfl
  have tDecl : CTyped objectChurch .nil impDecl cU1 :=
    cpiT (craise (const_U0_typed (by decide))) (cpiT (craise (const_U0_typed (by decide)))
      (craise (const_U0_typed (by decide))))
  have rel := h declared (.sort _) tDecl natImpReading_adequateType cImpTele_formed natTok
    natImpReading_mem_natTok (by rw [natImpReading_cinterp_impDecl]; exact typedAt_natTok)
  have nonvac : ∀ y : Tok, ent [] y = false → ent [] (.fn .lam [] [] [y]) = false := fun y hy => by
    rw [ent_nil_lam1]
    exact hy
  have piRed : CRedTy objectHeadReduction cImpTele (impDecl.liftClosed : CTm Tower.Head 2)
      (.pi (.const propN) (.pi (.const propN) (.const propN))) :=
    CRedTy.refl ⟨_, .sort _, tDecl.substitute (Γ := .nil) (Δ := cImpTele)
      (σ := fun i => .var (Fin.elim0 i)) fun i => i.elim0⟩
  have hnv : ent [] natTok = false := nonvac _ (nonvac _ (ent_nil_tag _))
  rcases RT.tm_lam_iff.1 rel with hvac | hcl
  · exact absurd (hvac.symm.trans hnv) (by decide)
  have tP : CTyped objectChurch cImpTele (.var 1) (.const propN) := .var 1
  obtain ⟨h₁, -⟩ := (hcl _ _ piRed).1 (.var 1) (.var 1) (.refl tP)
    (fun _ hx => absurd hx List.not_mem_nil) _ List.mem_cons_self
  have piRed₂ : CRedTy objectHeadReduction cImpTele (.pi (.const propN) (.const propN))
      (.pi (.const propN) (.const propN)) :=
    CRedTy.refl ⟨_, .sort _, cpiT (craise (const_U0_typed (by decide)))
      (craise (const_U0_typed (by decide)))⟩
  rcases RT.tm_lam_iff.1 h₁ with hvac | hcl₂
  · rw [nonvac _ (ent_nil_tag _)] at hvac
    cases hvac
  have tQ : CTyped objectChurch cImpTele (.var 0) (.const propN) := .var 0
  obtain ⟨h₂, -⟩ := (hcl₂ _ _ piRed₂).1 (.var 0) (.var 0) (.refl tQ)
    (fun _ hx => absurd hx List.not_mem_nil) _ List.mem_cons_self
  rcases (RT.tm_type_iff rfl).1 h₂ with hvac | ⟨u, -, hU, -⟩ | ⟨-, hnum⟩
  · rw [ent_nil_tag] at hvac
    cases hvac
  · exact CRedTy.head_ne_prop hU (propRed objectExtension)
  · obtain ⟨redNum, -⟩ := RT.ty_nat_iff.1 hnum
    have e := CRedTy.nf_unique redNum impVars_decode_red objectHeadReduction.normal_num
      (objectHeadReduction.normal_pi _ _)
    cases e

end NatImplication

/-! ## The ground types -/

/-- **A token of the numbers is typed at them**, unlike every token at the sets
(`not_typedAt_groundI`). -/
theorem typedAt_natI_zero : TypedAt natI (.tag .zero) :=
  ⟨Elem.nat, Ideal.below_nat, Ideal.nat_type, tyTok_tag_zero.2 List.mem_cons_self⟩

/-! ## The erasure of matching forms -/

/-- **Equal annotated dependent function types over the numbers erase to matching raw
types.** -/
theorem formsMatch_piNumNum_erase :
    FormsMatch objectRules objectRoles .nil (.pi (.const numN) (.const numN))
      (.pi (.const numN) (.const numN)) := by
  have facts := objectFormFacts
  have m := facts.forms (Γ := .nil) (A := .pi cnum cnum) (B := .pi cnum cnum)
    ⟨_, .sort Tower.zero, .refl (cpiT cnum_typed cnum_typed)⟩ .nil (.inr (.inl ⟨_, _, rfl⟩))
    (.inr (.inl ⟨_, _, rfl⟩))
  exact m.erase

/-! ## The recursor needs the step at its numeral -/

section Core

open ValidityControls (coreReduction)
open FundamentalControls (coreReduction_decoderStuck adequate_czero_at)

variable {A : DeclName → Bool} {n : Nat} {Γ : CCtx Tower.Head n}

/-- The identity on the numbers applied to zero, a β-redex. -/
abbrev idZero {n : Nat} : CTm Tower.Head n := .app (.lam cnum (.var 0)) czero

/-- `num-rec (λ _. num) 1 (λ m h. suc h) ((λ x. x) 0)`. -/
abbrev recStuck : CTm Tower.Head 0 := cRecApp motiveNum cOne sucStepAt idZero

/-- The constants of `recStuck`: `num`, `zero`, `suc` and `num-rec`. -/
abbrev recAllowed : DeclName → Bool := allowedIn [numN, zeroN, sucN, numRecName]

theorem motiveNum_typed_within (hn : A numN = true) :
    CTyped (objectChurch.restrict A) Γ motiveNum (.pi cnum cU0) :=
  .lamIntro (cnum_typed_within hn) (.sort _)
    (cpiT_within (craise_within (cnum_typed_within hn)) cU0_typed_within) (.sort _)
    (cnum_typed_within hn)

theorem motiveNum_beta_within (hn : A numN = true) {a : CTm Tower.Head n}
    (ta : CTyped (objectChurch.restrict A) Γ a cnum) :
    CEqual (objectChurch.restrict A) Γ (.app motiveNum a) cnum cU0 :=
  CDerivable.betaPi (cpiT_within (craise_within (cnum_typed_within hn)) cU0_typed_within) (.sort _)
    (cnum_typed_within hn) ta

theorem sucStepAt_typed_within (hn : A numN = true) (hs : A sucN = true) :
    CTyped (objectChurch.restrict A) Γ sucStepAt
      (.pi cnum (.pi (.app motiveNum (.var 0)) (.app motiveNum (csuc (.var 1))))) := by
  have tPx : CTyped (objectChurch.restrict A) (.snoc Γ cnum) (.app motiveNum (.var 0)) cU0 :=
    .appElim (B := cU0) (motiveNum_typed_within hn) (.var 0)
  have h : CTyped (objectChurch.restrict A) (.snoc (.snoc Γ cnum) (.app motiveNum (.var 0)))
      (.var 0) cnum :=
    .conv (.var 0) (motiveNum_beta_within hn (.var 1)) (.sort _)
  have body : CTyped (objectChurch.restrict A) (.snoc (.snoc Γ cnum) (.app motiveNum (.var 0)))
      (csuc (.var 0)) (.app motiveNum (csuc (.var 1))) :=
    .conv (csuc_typed_within hs hn h)
      (.symm (motiveNum_beta_within hn (csuc_typed_within hs hn (.var 1)))) (.sort _)
  have tPi₂ : CTyped (objectChurch.restrict A) (.snoc Γ cnum)
      (.pi (.app motiveNum (.var 0)) (.app motiveNum (csuc (.var 1)))) cU0 :=
    cpiT_within tPx (.appElim (B := cU0) (motiveNum_typed_within hn) (csuc_typed_within hs hn (.var 1)))
  exact .lamIntro (cnum_typed_within hn) (.sort _) (cpiT_within (cnum_typed_within hn) tPi₂) (.sort _)
    (.lamIntro tPx (.sort _) tPi₂ (.sort _) body)

/-- The annotated type of `num-rec`, formed within the numbers, zero and the successor. -/
theorem cnumRecType_formed_within (hn : A numN = true) (hz : A zeroN = true)
    (hs : A sucN = true) :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.numRecType) cU1 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi (.pi cnum cU0) (.pi (.app (.var 0) czero)
      (.pi (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1)))))
        (.pi cnum (.app (.var 3) (.var 0)))))) cU1
  have tMotive : CTyped (objectChurch.restrict A) .nil (.pi cnum cU0) cU1 :=
    cpiT_within (craise_within (cnum_typed_within hn)) cU0_typed_within
  have tZeroCase : CTyped (objectChurch.restrict A) (.snoc .nil (.pi cnum cU0))
      (.app (.var 0) czero) cU0 :=
    .appElim (B := cU0) (.var 0) (czero_typed_within hz hn)
  have tHyp : CTyped (objectChurch.restrict A)
      (.snoc (.snoc (.snoc .nil (.pi cnum cU0)) (.app (.var 0) czero)) cnum)
      (.app (.var 2) (.var 0)) cU0 :=
    .appElim (B := cU0) (.var 2) (.var 0)
  have tGoal : CTyped (objectChurch.restrict A)
      (.snoc (.snoc (.snoc (.snoc .nil (.pi cnum cU0)) (.app (.var 0) czero)) cnum)
        (.app (.var 2) (.var 0)))
      (.app (.var 3) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (.var 3) (csuc_typed_within hs hn (.var 1))
  have tSucCase : CTyped (objectChurch.restrict A)
      (.snoc (.snoc .nil (.pi cnum cU0)) (.app (.var 0) czero))
      (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1))))) cU0 :=
    cpiT_within (cnum_typed_within hn) (cpiT_within tHyp tGoal)
  have tBody : CTyped (objectChurch.restrict A)
      (.snoc (.snoc (.snoc (.snoc .nil (.pi cnum cU0)) (.app (.var 0) czero))
        (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1)))))) cnum)
      (.app (.var 3) (.var 0)) cU0 :=
    .appElim (B := cU0) (.var 3) (.var 0)
  exact cpiT_within tMotive (cpiT_within (craise_within tZeroCase) (cpiT_within (craise_within tSucCase)
    (cpiT_within (craise_within (cnum_typed_within hn)) (craise_within tBody))))

theorem recStuck_typed_within (hn : A numN = true) (hz : A zeroN = true) (hs : A sucN = true)
    (hr : A numRecName = true) :
    CTyped (objectChurch.restrict A) .nil recStuck (.app motiveNum idZero) := by
  have tId : CTyped (objectChurch.restrict A) .nil idZero cnum :=
    .appElim (B := cnum) (.lamIntro (cnum_typed_within hn) (.sort _)
      (cpiT_within (cnum_typed_within hn) (cnum_typed_within hn)) (.sort _) (.var 0))
      (czero_typed_within hz hn)
  have tOne : CTyped (objectChurch.restrict A) .nil cOne (.app motiveNum czero) :=
    .conv (csuc_typed_within hs hn (czero_typed_within hz hn))
      (.symm (motiveNum_beta_within hn (czero_typed_within hz hn))) (.sort _)
  have r1 := CDerivable.appElim (cconst_within (Γ := .nil) Package.numRecType hr (by decide)
    (by decide) (cnumRecType_formed_within hn hz hs)) (motiveNum_typed_within hn)
  have r2 := CDerivable.appElim r1 tOne
  have r3 := CDerivable.appElim r2 (sucStepAt_typed_within hn hs)
  exact CDerivable.appElim r3 tId

theorem recStuck_typed : CTyped objectChurch .nil recStuck (.app motiveNum idZero) :=
  CDerivable.mono ChurchRules.restrict_sub (recStuck_typed_within (A := recAllowed) rfl rfl rfl rfl)

theorem cinterp_idZero :
    cinterp objectChurchReading (idZero : CTm Tower.Head 0) Env.nil =
      cinterp objectChurchReading (czero : CTm Tower.Head 0) Env.nil := by
  change Ideal.app (Ideal.clam (objectChurchReading.const numN) fun y => y)
    (objectChurchReading.const zeroN) = objectChurchReading.const zeroN
  rw [Ideal.app_clam Ideal.Cont.id, objectChurchReading_num, objectChurchReading_zero,
    Ideal.projT_natI_zeroI]

/-- The successor tag is a token of the denotation of `recStuck`, as of the recursion at
zero. -/
theorem recStuck_mem_succ : (cinterp objectChurchReading recStuck Env.nil).Mem (.tag .succ) := by
  change (Ideal.app (cinterp objectChurchReading
    (CTm.app (.app (.app (.const numRecName) motiveNum) cOne) sucStepAt : CTm Tower.Head 0)
      Env.nil) (cinterp objectChurchReading idZero Env.nil)).Mem _
  rw [cinterp_idZero]
  exact recZeroOne_mem_succ

theorem typedAt_motiveIdZero_succ :
    TypedAt (cinterp objectChurchReading (.app motiveNum idZero : CTm Tower.Head 0) Env.nil)
      (.tag .succ) := by
  change TypedAt (Ideal.app (Ideal.clam (objectChurchReading.const numN)
    fun _ => objectChurchReading.const numN) (cinterp objectChurchReading idZero Env.nil)) _
  rw [Ideal.app_clam (Ideal.Cont.const _), objectChurchReading_num]
  exact ⟨Elem.nat, Ideal.below_nat, Ideal.nat_type, tyTok_tag_succ.2 List.mem_cons_self⟩

/-- **Under the object package's reduction the recursion reduces to a successor**, read off
the relation: its numeral `(λ x. x) 0` reduces first, at the recursor's numeral. -/
theorem recStuck_reduces_suc :
    ∃ m, CRedTm objectHeadReduction .nil recStuck (csuc m) (.app motiveNum idZero) := by
  have valid := objectChurch_fundamental recStuck_typed CCtxFormed.nil
  have rel := valid.1 Env.nil trivial CCtxFormed.nil SubstRel.nil (.tag .succ) recStuck_mem_succ
    typedAt_motiveIdZero_succ
  obtain ⟨m, -, -, red, -, -⟩ := RT.tm_succTag_iff.1 rel
  exact ⟨m, red⟩

/-- **`recStuck` takes no core step**: it is no root redex, since its numeral takes a step,
and its function is a spine of the recursor below its arity. -/
theorem recStuck_normal : coreReduction.Normal recStuck := by
  have role : objectRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
    objectRoles_of_roles roles_numRec nofun
  intro u s
  cases s with
  | root root =>
      have root' : objectChurch.computation.step
          (CTm.appSpine (.const numRecName) ([motiveNum, cOne, sucStepAt] ++ idZero :: [])) u :=
        root
      exact CWhStepR.not_scrutinee_of_root objectShape role root' _ (CWhStepR.beta _ _ _)
  | appFun _ s =>
      exact CWhStepR.not_fun_of_spine objectShape role
        (args := [motiveNum, cOne, sucStepAt, idZero]) rfl rfl _ (s.step objectHeadReduction)

/-- **The recursor's constants are not all adequate under the core reduction**: the relation
at the successor tag would have `recStuck` reduce to a successor, and it takes no core
step. -/
theorem recAllowed_not_adequate_core :
    ¬ ∀ {c : DeclName}, recAllowed c = true → ConstAdequateAt objectChurchReading coreReduction c :=
  fun consts => by
    have valid := CDerivable.valid ConvRules.objectLevels objectChurchReading_valid
      objectExtension.groundHeads objectRules_groundHeadEq coreReduction_decoderStuck consts
      (recStuck_typed_within rfl rfl rfl rfl) CCtxFormed.nil
    have rel := valid.1 Env.nil trivial (Δ := .nil) .nil SubstRel.nil (.tag .succ)
      recStuck_mem_succ typedAt_motiveIdZero_succ
    obtain ⟨m, -, -, red, -, -⟩ := RT.tm_succTag_iff.1 rel
    have e := coreReduction.red_normal recStuck_normal red.1
    cases e

/-- The relation of a variable of type `num`, under every head reduction. -/
theorem SubstRel.numVar_at {H : HeadReduction objectChurch objectRigid} {m : Nat}
    {Γ : CCtx Tower.Head n} {ρ : Env n} {Δ : CCtx Tower.Head m} {σ σ' : CSub Tower.Head n m}
    {i : Fin n} (hi : Γ.lookup i = cnum) (hσ : SubstRel objectChurchReading H Γ ρ Δ σ σ') :
    ∀ y, (projT natI (ρ i)).Mem y → RT H Δ true y cnum (σ i) (σ' i) := by
  intro y hy
  obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hy
  refine RT.closed' e fun t ht => ?_
  have h := (hσ.2 i).2.2 t (hv t ht) (by rw [hi, cinterp_cnum]; exact hvT t ht)
  rwa [hi] at h

/-- `suc` is adequate under every head reduction. -/
theorem constAdequateAt_suc_at (H : HeadReduction objectChurch objectRigid) :
    ConstAdequateAt objectChurchReading H sucN := by
  refine ConstAdequateAt.of_spine (Θ := .snoc .nil cnum) (T := cnum) ConvRules.objectLevels
    objectChurch_soundnessFacts
    (objectChurch_declared (c := sucN) (T := .pi Package.numT Package.numT) (by decide) rfl)
    (csuc_typed (.var 0)) ?_
  intro ρ fits m Δ σ σ' formed hσ s hs _
  change (Ideal.app (objectChurchReading.const sucN) (ρ 0)).Mem s at hs
  rw [objectChurchReading_suc, app_sucConst objectChurchReading numNames
    objectChurchReading_num] at hs
  have h0 := SubstRel.numVar_at (i := 0) rfl hσ
  have e0 : CEqual objectChurch Δ (σ 0) (σ' 0) cnum := hσ.1.2 0
  obtain ⟨t0, t0'⟩ := CEqual.typed ConvRules.objectLevels e0 formed
  have red : SuccRed H Δ cnum (csuc (σ 0)) (csuc (σ' 0)) (σ 0) (σ' 0) :=
    ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, CRedTm.refl (csuc_typed t0),
      CRedTm.refl (csuc_typed t0'), e0⟩
  obtain ⟨v, hv, e⟩ := hs
  refine RT.closed' e fun t ht => ?_
  rcases hv t ht with rfl | ⟨r, rfl, hr⟩
  · exact RT.tm_succTag_iff.2 ⟨_, _, red⟩
  · exact RT.tm_argSucc_iff.2 (.inr ⟨_, _, red, fun _ h => absurd h List.not_mem_nil,
      fun _ => h0 r hr⟩)

/-- **The recursor is not adequate under the core reduction**, while `num`, `zero` and
`suc` are: its adequacy needs the step at its numeral. -/
theorem numRec_not_constAdequate_core :
    ¬ ConstAdequateAt objectChurchReading coreReduction numRecName := by
  intro hrec
  refine recAllowed_not_adequate_core (consts_allowedIn fun c hc => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ConstAdequateAt.of_adequate (objectChurch_declared (c := numN) (T := Package.U0)
      (by decide) rfl) ((adequateType_typeAt objectExtension (H := coreReduction) (.base .num)
        (.nil : CCtx Tower.Head 0)).adequate ConvRules.objectLevels objectChurch_soundnessFacts
          (.sort Tower.zero))
  · exact ConstAdequateAt.of_adequate (objectChurch_declared (c := zeroN) (T := Package.numT)
      (by decide) rfl) (adequate_czero_at coreReduction)
  · exact constAdequateAt_suc_at coreReduction
  · exact hrec

end Core

end AdequacyControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
