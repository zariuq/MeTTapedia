import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchSigmaControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchModelControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectHeadReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.CoreHeadReduction

/-!
# Controls: symmetry of the relation needs the type's relation to itself

The laws of the term relation read the type's relation to itself as far as the type
witness observes (`RT.symm`, `RT.trans`); the application case of the fundamental lemma
composes the two halves of the function clause by transitivity at the family's value,
related to itself by the dependent function type's adequacy. This module shows at the
object package that the presupposition cannot be dropped.

* **A typed term equal to `0` that takes no core step** (`stuckZero_normal`):
  `add 0 (add 0 0)` is equal to `0` (`stuckZero_eq`), but its numeral `add 0 0` is not
  in constructor form, and the core weak-head reduction has no step at an inspected
  argument.
* **Negative: an asymmetric pair of related pairs** (`symm_presupposition_needed`). At
  `Σ (x : num). Id num x x`, the token `arg pair 1 [] (arg refl 0 [] (tag zero))` is typed
  at a compact type witness of that type (`typed_symmToken`). Under the core weak-head
  reduction, `(0, refl 0)` is related to `(add 0 (add 0 0), refl 0)` there
  (`pairs_related`), but not the other way (`pairs_not_symm`): read at the second
  pair's first component, the reflexivity's point must be related to the endpoint
  `add 0 (add 0 0)` at the tag of zero, and that endpoint does not reduce to `0`. By
  symmetry of the relation (`RT.symm`), the type is therefore not related to itself as
  far as the witness observes.
* **Positive: with the scrutinee steps** (`pairs_symm_objectHeadReduction`). Under the
  object package's weak-head reduction the numeral reduces, and the pairs are related
  the other way too.
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

namespace CodeModel
namespace ValidityControls

open SigmaControls (sigId sigId_typed pairRefl pairRefl_typed ty_nat_univ)

/-! ## The core weak-head reduction and a numeral it cannot reduce -/

/-- The core weak-head reduction of the object package: no step at an inspected
argument. -/
abbrev coreReduction : HeadReduction objectChurch objectRigid := objectHeadReduction.core

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- `add 0 (add 0 0)`. -/
abbrev stuckZero : CTm Tower.Head n := cadd czero (cadd czero czero)

theorem stuckZero_typed : CTyped objectChurch Γ stuckZero cnum :=
  cadd_typed czero_typed (cadd_typed czero_typed czero_typed)

/-- `add 0 (add 0 0) ≡ 0 : num`. -/
theorem stuckZero_eq : CEqual objectChurch Γ stuckZero czero cnum := by
  have e₁ : CEqual objectChurch Γ (cadd czero czero) czero cnum :=
    .rootAdmitted (caddZero_step czero) (caddZero_admits czero_typed)
      (cadd_typed czero_typed czero_typed) czero_typed
  have e₂ : CEqual objectChurch Γ stuckZero (cadd czero czero) cnum :=
    CTyped.instantiateEq (cadd_typed (Γ := .snoc Γ cnum) czero_typed (.var 0))
      (cadd_typed czero_typed czero_typed) e₁
  exact .trans e₂ e₁

/-- **`add 0 (add 0 0)` takes no core step**: it is no root redex, since its numeral
takes a step, and its function `add 0` is a spine below the arity of addition. -/
theorem stuckZero_normal : coreReduction.Normal (stuckZero : CTm Tower.Head n) := by
  intro u s
  cases s with
  | root root =>
      have root' : objectChurch.computation.step
          (CTm.appSpine (.const addN) ([czero] ++ cadd czero czero :: [])) u := root
      exact CWhStepR.not_scrutinee_of_root objectShape objectRoles_add root' _
        (CWhStepR.root (caddZero_step czero))
  | appFun _ s =>
      exact CWhStepR.not_fun_of_spine objectShape objectRoles_add
        (args := [czero, cadd czero czero]) rfl rfl _ (s.step objectHeadReduction)

/-! ## The token and its witness -/

/-- The identity type `Id num 0 0`, as a compact element. -/
def identWitness : List Tok := Elem.ident Elem.nat Elem.zero Elem.zero

/-- A compact witness of `Σ (x : num). Id num x x`, whose family entry has the empty
input. -/
def symmWitness : List Tok := Elem.former .sigma Elem.nat [([], identWitness)]

/-- The second-component token: the second projection is a reflexivity whose point
entails zero, with no dependency on the first component. -/
def symmToken : Tok := .arg .pair 1 [] (.arg .refl 0 [] (.tag .zero))

theorem typed_symmToken : Ty symmWitness Elem.univ ∧ TyTok symmWitness symmToken := by
  have hzero : Ty Elem.zero Elem.nat := Elem.ty_zero List.mem_cons_self
  have hW : Ty identWitness Elem.univ := Elem.ty_ident Elem.isUniv_univ ty_nat_univ hzero hzero
  refine ⟨Elem.ty_former (.inr rfl) Elem.isUniv_univ ty_nat_univ fun p hp => ?_, ?_⟩
  · rw [List.mem_singleton.1 hp]
    exact ⟨fun _ h => absurd h List.not_mem_nil, hW⟩
  · refine tyTok_snd.2 ⟨List.mem_cons_self, fun _ h => absurd h List.not_mem_nil, ?_⟩
    -- the family's value at the empty input holds the identity type's witness
    have hsub : identWitness ⊑ fnApp .sigma symmWitness [] :=
      Le.of_subset fun t ht => mem_fnApp.2 ⟨Elem.nat, [], identWitness,
        List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self),
        fun _ h => absurd h List.not_mem_nil, ht⟩
    refine TyTok.mono hsub ?_
    -- the reflexivity at `0` is an element of `Id num 0 0`
    have hnat : Tok.tag .nat ∈ args .ident 0 identWitness :=
      mem_args_of_arg (C := []) (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map_of_mem List.mem_cons_self))))
    have h1 : Tok.tag .zero ∈ args .ident 1 identWitness :=
      mem_args_of_arg (C := Elem.nat) (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self))))
    have h2 : Tok.tag .zero ∈ args .ident 2 identWitness :=
      mem_args_of_arg (C := Elem.nat) (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map_of_mem List.mem_cons_self)))
    have hrefl : Ty (Elem.refl Elem.zero) identWitness :=
      (Elem.ty_refl List.mem_cons_self).2 ⟨Elem.ty_zero hnat,
        fun t ht => by rw [List.mem_singleton.1 ht]; exact ent_of_mem h1,
        fun t ht => by rw [List.mem_singleton.1 ht]; exact ent_of_mem h2⟩
    exact hrefl _ (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))

/-! ## The pairs -/

/-- The pair `(add 0 (add 0 0), refl 0)`. -/
abbrev pairStuck : CTm Tower.Head n := .pair stuckZero (.refl czero)

/-- `Id num 0 0 ≡ Id num N N` for every `N ≡ 0`. -/
theorem idZero_eq {N : CTm Tower.Head n} (e : CEqual objectChurch Γ czero N cnum) :
    CTypeEq objectChurch Γ (.id cnum czero czero) (.id cnum N N) :=
  ⟨.sort Tower.zero, .sort _, .idCong (.refl cnum_typed) (.sort _) e e⟩

theorem reflZero_typed_stuck :
    CTyped objectChurch Γ (.refl czero) (.id cnum stuckZero stuckZero) :=
  CTyped.convType (.reflIntro czero_typed) (idZero_eq (.symm stuckZero_eq))

theorem pairStuck_typed : CTyped objectChurch Γ pairStuck sigId :=
  .pairIntro sigId_typed (.sort _) stuckZero_typed reflZero_typed_stuck

theorem betaFst_refl : CEqual objectChurch Γ (.fst pairRefl) czero cnum :=
  .betaFst sigId_typed (.sort _) czero_typed (.reflIntro czero_typed)

theorem betaFst_stuck : CEqual objectChurch Γ (.fst pairStuck) stuckZero cnum :=
  .betaFst sigId_typed (.sort _) stuckZero_typed reflZero_typed_stuck

/-- The two pairs have equal first projections. -/
theorem fst_pairs_eq : CEqual objectChurch Γ (.fst pairRefl) (.fst pairStuck) cnum :=
  .trans betaFst_refl (.trans (.symm stuckZero_eq) (.symm betaFst_stuck))

section Related

variable {H : HeadReduction objectChurch objectRigid} {L : Type} [LevelOrder L]
  (levels : LevelModel objectRules L) (formed : CCtxFormed objectChurch Γ)

include levels formed in
/-- The second projections of the two pairs are related at `Id num N N` as far as the
point token observes, for every `N` that reduces to `0`. -/
theorem snd_pairs_related {N : CTm Tower.Head n} (hN : CRedTm H Γ N czero cnum) :
    RT H Γ true (.arg .refl 0 [] (.tag .zero)) (.id cnum N N) (.snd pairRefl) (.snd pairStuck) ∧
      RT H Γ true (.arg .refl 0 [] (.tag .zero)) (.id cnum N N) (.snd pairStuck)
        (.snd pairRefl) := by
  have e0N : CEqual objectChurch Γ czero N cnum := .symm hN.2
  have eId := idZero_eq e0N
  have eId' : CTypeEq objectChurch Γ (.id cnum stuckZero stuckZero) (.id cnum N N) :=
    CTypeEq.trans levels (idZero_eq (.symm stuckZero_eq)).symm eId
  have idType : CIsType objectChurch Γ (.id cnum N N) := (CTypeEq.isType levels eId formed).2
  have sndRefl : CRedTm H Γ (.snd pairRefl) (.refl czero) (.id cnum N N) :=
    ⟨.single (H.sndPair _ _),
      CEqual.convType (.betaSnd sigId_typed (.sort _) czero_typed (.reflIntro czero_typed)) eId⟩
  have sndStuck : CRedTm H Γ (.snd pairStuck) (.refl czero) (.id cnum N N) :=
    ⟨.single (H.sndPair _ _),
      CEqual.convType (.betaSnd sigId_typed (.sort _) stuckZero_typed reflZero_typed_stuck) eId'⟩
  have numRed : CRedTy H Γ (cnum : CTm Tower.Head n) cnum := CRedTy.refl ⟨_, .sort _, cnum_typed⟩
  have z00 : RT H Γ true (.tag .zero) cnum czero czero :=
    RT.tm_zero_iff.2 ⟨numRed, CRedTm.refl czero_typed, CRedTm.refl czero_typed⟩
  have z0N : RT H Γ true (.tag .zero) cnum czero N :=
    RT.tm_zero_iff.2 ⟨numRed, CRedTm.refl czero_typed, hN⟩
  exact ⟨RT.tm_argRefl_iff.2 (.inr ⟨cnum, N, N, czero, czero,
      ⟨CRedTy.refl idType, sndRefl, sndStuck, e0N, e0N, .refl czero_typed⟩,
      fun _ h => absurd h List.not_mem_nil, fun _ => ⟨z0N, z0N, z00⟩⟩),
    RT.tm_argRefl_iff.2 (.inr ⟨cnum, N, N, czero, czero,
      ⟨CRedTy.refl idType, sndStuck, sndRefl, e0N, e0N, .refl czero_typed⟩,
      fun _ h => absurd h List.not_mem_nil, fun _ => ⟨z0N, z0N, z00⟩⟩)⟩

/-- At a weak-head reduction in which the first projection of the left pair reduces to
`0`, the left pair is related to the right one at the token, when the pairs have equal
first projections and their second projections are related at `Id num N N` for every
`N` that reduces to `0`. -/
theorem pairs_related_of {M M' : CTm Tower.Head n}
    (hsnd : ∀ {N : CTm Tower.Head n}, CRedTm H Γ N czero cnum →
      RT H Γ true (.arg .refl 0 [] (.tag .zero)) (.id cnum N N) (.snd M) (.snd M'))
    (efst : CEqual objectChurch Γ (.fst M) (.fst M') cnum)
    (fstRed : CRedTm H Γ (.fst M) czero cnum) : RT H Γ true symmToken sigId M M' := by
  refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
  have e := H.red_normal (H.normal_sigma _ _) hT.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨efst, fun c hc => absurd hc List.not_mem_nil, fun h => absurd h (by decide),
    fun _ N Q hQ hNQ => hsnd (CRedTm.trans hNQ (CRedTm.reduce_same hQ fstRed H.normal_zero))⟩

end Related

/-! ## The controls -/

variable {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
  (formed : CCtxFormed objectChurch Γ)

include levels formed in
/-- **Under the core reduction, `(0, refl 0)` is related to `(add 0 (add 0 0), refl 0)`**
at the token. -/
theorem pairs_related : RT coreReduction Γ true symmToken sigId pairRefl pairStuck :=
  pairs_related_of (fun hN => (snd_pairs_related levels formed hN).1) fst_pairs_eq
    ⟨.single (coreReduction.fstPair _ _), betaFst_refl⟩

/-- **Negative: under the core reduction the relation is not symmetric there.** Read at
the second pair's first component `add 0 (add 0 0)`, the reflexivity's point must be
related at the tag of zero to that endpoint, which takes no core step. -/
theorem pairs_not_symm : ¬ RT coreReduction Γ true symmToken sigId pairStuck pairRefl := by
  intro h
  have notVac : ent ([] : List Tok) (.arg .refl 0 [] (.tag .zero)) = false := by
    cases e : ent ([] : List Tok) (.arg .refl 0 [] (.tag .zero)) with
    | false => rfl
    | true =>
        have e' := vacuous_arg e
        rw [ent_nil_tag] at e'
        cases e'
  rcases RT.tm_argPair_iff.1 h with hvac | hcl
  · rw [vacuous_arg hvac] at notVac
    cases notVac
  obtain ⟨-, -, -, h1⟩ := hcl cnum (.id cnum (.var 0) (.var 0)) (CRedTy.refl ⟨_, .sort _, sigId_typed⟩)
  have fstRed : CRedTm coreReduction Γ (.fst pairStuck) stuckZero cnum :=
    ⟨.single (coreReduction.fstPair _ _), betaFst_stuck⟩
  rcases RT.tm_argRefl_iff.1 (h1 rfl stuckZero stuckZero fstRed (CRedTm.refl stuckZero_typed))
    with hvac | ⟨B, x, y, r, r', hr, -, hpt⟩
  · rw [hvac] at notVac
    cases notVac
  have e := coreReduction.red_normal (coreReduction.normal_id _ _ _) hr.1.1
  injection e with _ eB ex ey
  subst eB ex ey
  obtain ⟨-, -, hx⟩ := RT.tm_zero_iff.1 (hpt rfl).1
  have e' := coreReduction.red_normal stuckZero_normal hx.1
  cases e'

include levels formed in
/-- **The type is not related to itself as far as the witness observes, under the core
reduction**: otherwise symmetry of the relation (`RT.symm`) would relate the pairs the
other way. -/
theorem sigId_not_self :
    ¬ ∀ s ∈ symmWitness, RT coreReduction Γ false s sigId sigId sigId := fun hT =>
  pairs_not_symm (RT.symm levels formed typed_symmToken.1 typed_symmToken.2 hT
    (pairs_related levels formed))

/-- **Negative control: symmetry of the term relation needs the type's relation to
itself.** In the empty context, at the object package's level model and core weak-head
reduction: the token is typed at a witness of `Σ (x : num). Id num x x`, the pairs are
related one way and not the other, and the type is not related to itself as far as the
witness observes. -/
theorem symm_presupposition_needed :
    (Ty symmWitness Elem.univ ∧ TyTok symmWitness symmToken) ∧
      RT coreReduction .nil true symmToken sigId pairRefl pairStuck ∧
      ¬ RT coreReduction .nil true symmToken sigId pairStuck pairRefl ∧
      ¬ ∀ s ∈ symmWitness, RT coreReduction .nil false s sigId sigId sigId :=
  ⟨typed_symmToken, pairs_related ConvRules.objectLevels .nil, pairs_not_symm,
    sigId_not_self ConvRules.objectLevels .nil⟩

include levels formed in
/-- **Positive: with the scrutinee steps the pairs are related both ways.** Under the
object package's weak-head reduction, `add 0 (add 0 0)` reduces to `0`. -/
theorem pairs_symm_objectHeadReduction :
    RT objectHeadReduction Γ true symmToken sigId pairRefl pairStuck ∧
      RT objectHeadReduction Γ true symmToken sigId pairStuck pairRefl := by
  have stuckRed : CRedTm objectHeadReduction Γ stuckZero czero cnum :=
    ⟨(Relation.ReflTransGen.single (objectExtension.head_add
      (objectHeadReduction.root (caddZero_step czero)))).tail
        (objectHeadReduction.root (caddZero_step czero)), stuckZero_eq⟩
  have fstRefl : CRedTm objectHeadReduction Γ (.fst pairRefl) czero cnum :=
    ⟨.single (objectHeadReduction.fstPair _ _), betaFst_refl⟩
  have fstStuck : CRedTm objectHeadReduction Γ (.fst pairStuck) czero cnum :=
    CRedTm.trans ⟨.single (objectHeadReduction.fstPair _ _), betaFst_stuck⟩ stuckRed
  exact ⟨pairs_related_of (fun hN => (snd_pairs_related levels formed hN).1) fst_pairs_eq fstRefl,
    pairs_related_of (fun hN => (snd_pairs_related levels formed hN).2) (.symm fst_pairs_eq)
      fstStuck⟩

end ValidityControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
