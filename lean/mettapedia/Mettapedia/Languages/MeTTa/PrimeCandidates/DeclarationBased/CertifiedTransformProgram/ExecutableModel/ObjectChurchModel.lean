import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ChurchRoots

/-!
# The object package's annotation is sound in the domain

The object reading (`objectChurchReading`) validates the annotation of the object package
(`objectChurchReading_valid : ReadingValid objectChurchReading objectChurch`):

* universes denote the universe, heads denote types, and head equality is respected
  (through the object package's level model);
* every declared constant denotes an element of its declared type
  (`objectChurchReading_constants`);
* **every rewrite schema is valid** (`objectSchemas_valid`): at every instance whose left
  side has spine facts at a type of which its right side is an element, both sides
  denote alike. Schema by schema:
  * the identity eliminator's rule, by the reflexivity fact of its path
    (`jAlignedConst_linear`);
  * both rules of `num-rec` (`nrConst_iotaZero`, `nrConst_iotaSucc`);
  * the equations of addition, of the iterated power set and of the iterator, by one
    unfolding of numeral recursion; the iterator's successor equation also by the
    projection of the recursive value onto the iterator's type at a count;
  * the seven definitions by one equation (`SpineFacts.defConst_root`);
  * the decoding of implication, and of every quantifier and equation instance
    (`Ideal.decode_impConst`, `Ideal.decode_allConst`, `Ideal.decode_eqConst`).

So every derivable statement of the object package's annotation holds in the domain
(`objectChurch_sound`), and the soundness facts of the relation's compatibility lemmas
hold for the object reading (`objectChurch_soundnessFacts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypeGenerated principal univIdeal
  codesIdeal natI zeroI groundI cpi instPi SpineTyped natRec)
open TelescopeAbstraction (applyClosed)
open FormationSensitiveHOLInterface (typeAt)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numT U0 eqAtTelescope transportTelescope composeTelescope)
open Mettapedia.Logic

namespace CodeModel

/-! ## Valid schemas -/

/-- A rewrite schema of the object package is **valid** in the object reading: at every
instance whose left side has spine facts at a type of which its right side is an element,
both sides denote alike. -/
def SchemaValid {k : Nat} (L R : Tm Tower.Head k) : Prop :=
  ∀ {n : Nat} (σ : CSub Tower.Head k n) {τ : Ideal} {ρ : Env n},
    SpineFacts objectChurchReading objectChurch ((elabLeft objectDecls L).subst σ) τ ρ →
    projT τ (cinterp objectChurchReading ((elabRight objectDecls L R).subst σ) ρ) =
      cinterp objectChurchReading ((elabRight objectDecls L R).subst σ) ρ →
    cinterp objectChurchReading ((elabLeft objectDecls L).subst σ) ρ =
      cinterp objectChurchReading ((elabRight objectDecls L R).subst σ) ρ

/-- A successor's argument, with spine facts, is a number. -/
theorem SpineFacts.sucArg {n : Nat} {m : CTm Tower.Head n} {T : Ideal} {ρ : Env n}
    (h : SpineFacts objectChurchReading objectChurch (.app (.const sucN) m) T ρ) :
    projT natI (cinterp objectChurchReading m ρ) = cinterp objectChurchReading m ρ := by
  obtain ⟨⟨-, spine⟩, -⟩ := SpineFacts.constSpine (args := [m])
    (objectChurch_declared (T := .pi numT numT) (by decide) rfl) h
  have h' := ((spineTyped_cinterp_pi objectChurchReading cnum cnum Env.nil _ []).1 spine).1
  rwa [cinterp_cnum] at h'

theorem cont₂_constStep (s : Ideal) : Ideal.Cont₂ fun (_ r : Ideal) => Ideal.app s r :=
  ⟨fun _ => Ideal.Cont.const _, fun _ => Ideal.cont₂_app.right s⟩

/-- The successor projects its argument onto the numbers. -/
theorem app_suc_projT (y : Ideal) :
    Ideal.app (sucConst objectChurchReading numNames) (projT natI y) =
      Ideal.app (sucConst objectChurchReading numNames) y := by
  rw [app_sucConst objectChurchReading numNames objectChurchReading_num,
    app_sucConst objectChurchReading numNames objectChurchReading_num, Ideal.projT_projT]

/-! ## The identity eliminator -/

theorem j_valid : SchemaValid (eliminatorLeft (Head := Tower.Head) jName) (.var 2) := by
  intro n σ τ ρ sl _
  have eL : elabLeft objectDecls (eliminatorLeft (Head := Tower.Head) jName) =
      CTm.appSpine (.const jName) [.var 5, .var 4, .var 3, .var 2, .var 1, .refl (.var 0)] := by
    decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [j_elabRight]
  have declared : objectChurch.constantType jName = some (liftTm Package.jType) :=
    objectChurch_declared (by decide) rfl
  obtain ⟨facts, -⟩ := SpineFacts.constSpine declared sl
  obtain ⟨T, hT, -⟩ := SpineFacts.reflArg declared (as := [σ 5, σ 4, σ 3, σ 2, σ 1])
    (bs := []) (a := σ 0) sl
  rw [cinterp_appSpine]
  change Ideal.appSpine (objectChurchReading.const jName) _ = _
  rw [objectChurchReading_j]
  exact jAlignedConst_linear objectChurchReading (.sort Tower.zero) facts ⟨T, hT⟩

/-! ## The recursor -/

theorem numRecZero_valid :
    SchemaValid (iotaLeft numRecName zeroN 2 0)
      (iotaRight numRecName 2 0 ([] : List CtorField)) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls (iotaLeft (Head := Tower.Head) numRecName zeroN 2 0) =
      CTm.appSpine (.const numRecName) [.var 2, .var 1, .var 0, .const zeroN] := by decide
  have eR : elabRight objectDecls (iotaLeft numRecName zeroN 2 0)
      (iotaRight numRecName 2 0 ([] : List CtorField)) = (.var 1 : CTm Tower.Head 3) := by decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  obtain ⟨facts, -⟩ := SpineFacts.constSpine
    (objectChurch_declared (T := Package.numRecType) (by decide) rfl) sl
  change Ideal.SpineFacts (nrTypeI objectChurchReading numNames)
    [cinterp objectChurchReading (σ 2) ρ, cinterp objectChurchReading (σ 1) ρ,
      cinterp objectChurchReading (σ 0) ρ, objectChurchReading.const zeroN] τ at facts
  rw [objectChurchReading_zero] at facts
  rw [cinterp_appSpine]
  change Ideal.appSpine (objectChurchReading.const numRecName)
    [cinterp objectChurchReading (σ 2) ρ, cinterp objectChurchReading (σ 1) ρ,
      cinterp objectChurchReading (σ 0) ρ, objectChurchReading.const zeroN] = _
  rw [objectChurchReading_numRec, objectChurchReading_zero]
  exact nrConst_iotaZero facts hr

theorem numRecSuc_valid :
    SchemaValid (iotaLeft numRecName sucN 2 1)
      (iotaRight numRecName 2 1 [(.recursive : CtorField)]) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls (iotaLeft (Head := Tower.Head) numRecName sucN 2 1) =
      CTm.appSpine (.const numRecName) [.var 3, .var 2, .var 1, .app (.const sucN) (.var 0)] := by
    decide
  have eR : elabRight objectDecls (iotaLeft numRecName sucN 2 1)
      (iotaRight numRecName 2 1 [(.recursive : CtorField)]) =
      (.app (.app (.var 1) (.var 0))
        (CTm.appSpine (.const numRecName) [.var 3, .var 2, .var 1, .var 0]) :
        CTm Tower.Head 4) := by
    decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  obtain ⟨facts, -⟩ := SpineFacts.constSpine
    (objectChurch_declared (T := Package.numRecType) (by decide) rfl) sl
  change Ideal.SpineFacts (nrTypeI objectChurchReading numNames)
    [cinterp objectChurchReading (σ 3) ρ, cinterp objectChurchReading (σ 2) ρ,
      cinterp objectChurchReading (σ 1) ρ,
      Ideal.app (objectChurchReading.const sucN) (cinterp objectChurchReading (σ 0) ρ)] τ at facts
  rw [objectChurchReading_suc] at facts
  change projT τ (Ideal.app
    (Ideal.app (cinterp objectChurchReading (σ 1) ρ) (cinterp objectChurchReading (σ 0) ρ))
    (Ideal.appSpine (objectChurchReading.const numRecName)
      [cinterp objectChurchReading (σ 3) ρ, cinterp objectChurchReading (σ 2) ρ,
        cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ])) = _ at hr
  rw [objectChurchReading_numRec] at hr
  rw [cinterp_appSpine]
  change Ideal.appSpine (objectChurchReading.const numRecName)
      [cinterp objectChurchReading (σ 3) ρ, cinterp objectChurchReading (σ 2) ρ,
        cinterp objectChurchReading (σ 1) ρ,
        Ideal.app (objectChurchReading.const sucN) (cinterp objectChurchReading (σ 0) ρ)] =
    Ideal.app
      (Ideal.app (cinterp objectChurchReading (σ 1) ρ) (cinterp objectChurchReading (σ 0) ρ))
      (Ideal.appSpine (objectChurchReading.const numRecName)
        [cinterp objectChurchReading (σ 3) ρ, cinterp objectChurchReading (σ 2) ρ,
          cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ])
  rw [objectChurchReading_numRec, objectChurchReading_suc]
  exact nrConst_iotaSucc objectChurchReading_num facts hr

/-! ## Addition and the iterated power set -/

theorem appSpine_addRaw (s a m : Ideal) :
    Ideal.appSpine (addRaw s) [a, m] = natRec a (fun _ r => Ideal.app s r) m := by
  have h₁ : Ideal.app (addRaw s) a =
      Ideal.lam fun M => natRec a (fun _ r => Ideal.app s r) (principal M) :=
    Ideal.app_lam_principal
      (H := fun z => Ideal.lam fun M => natRec z (fun _ r => Ideal.app s r) (principal M))
      (Ideal.cont_lam_param fun M => Ideal.cont_natRec_param (Z := fun z => z)
        (S := fun _ => fun _ r => Ideal.app s r) Ideal.Cont.id (fun _ _ => Ideal.Cont.const _)
        (fun _ => cont₂_constStep s) (principal M)) a
  have h₂ : Ideal.app (Ideal.lam fun M => natRec a (fun _ r => Ideal.app s r) (principal M)) m =
      natRec a (fun _ r => Ideal.app s r) m :=
    Ideal.app_lam_principal (Ideal.cont_natRec (cont₂_constStep s)) m
  show Ideal.app (Ideal.app (addRaw s) a) m = _
  rw [h₁, h₂]

theorem appSpine_powRaw (w n x : Ideal) :
    Ideal.appSpine (powRaw w) [n, x] = natRec x (fun _ r => Ideal.app w r) n := by
  have h₁ : Ideal.app (powRaw w) n =
      Ideal.lam fun X => natRec (principal X) (fun _ r => Ideal.app w r) n :=
    Ideal.app_lam_principal
      (H := fun ν => Ideal.lam fun X => natRec (principal X) (fun _ r => Ideal.app w r) ν)
      (Ideal.cont_lam_param fun _ => Ideal.cont_natRec (cont₂_constStep w)) n
  have h₂ : Ideal.app (Ideal.lam fun X => natRec (principal X) (fun _ r => Ideal.app w r) n) x =
      natRec x (fun _ r => Ideal.app w r) n :=
    Ideal.app_lam_principal (H := fun z => natRec z (fun _ r => Ideal.app w r) n)
      (Ideal.cont_natRec_param (Z := fun z => z) (S := fun _ => fun _ r => Ideal.app w r)
        Ideal.Cont.id (fun _ _ => Ideal.Cont.const _) (fun _ => cont₂_constStep w) n) x
  show Ideal.app (Ideal.app (powRaw w) n) x = _
  rw [h₁, h₂]

/-- Addition, as the Church constant of its function at its declared type. -/
theorem objectChurchReading_add_church :
    objectChurchReading.const addN = projT (cinterp objectChurchReading (liftTm addType) Env.nil)
      (addRaw (sucConst objectChurchReading numNames)) := by
  rw [objectChurchReading_const_of (show objConst addN = .add by decide)]
  show projT _ (addRaw (objectChurchReading.const sucN)) = _
  rw [objectChurchReading_suc]
  rfl

/-- The iterated power set, as the Church constant of its function at its declared type. -/
theorem objectChurchReading_pow_church :
    objectChurchReading.const powN = projT (cinterp objectChurchReading (liftTm powType) Env.nil)
      (powRaw (objectChurchReading.const powerN)) :=
  objectChurchReading_const_of (show objConst powN = .pow by decide)

/-- The power set projects its argument onto the sets. -/
theorem app_power_projT (y : Ideal) :
    Ideal.app (objectChurchReading.const powerN) (projT groundI y) =
      Ideal.app (objectChurchReading.const powerN) y := by
  have hf : projT (cpi groundI fun _ => groundI) (objectChurchReading.const powerN) =
      objectChurchReading.const powerN := by
    rw [objectChurchReading_power]
    exact Ideal.projT_projT _ _
  exact Ideal.app_projT_arg (Ideal.Cont.const groundI) hf y

theorem instPi_addType (a m : Ideal) :
    instPi (cinterp objectChurchReading (liftTm addType) Env.nil) [a, m] = natI := by
  rw [show (liftTm addType : CTm Tower.Head 0) = .pi cnum (.pi cnum cnum) from rfl,
    instPi_cinterp_pi, instPi_cinterp_pi]
  exact cinterp_cnum _

theorem instPi_powType (n x : Ideal) :
    instPi (cinterp objectChurchReading (liftTm powType) Env.nil) [n, x] = groundI := by
  rw [show (liftTm powType : CTm Tower.Head 0) = .pi cnum (.pi cset cset) from rfl,
    instPi_cinterp_pi, instPi_cinterp_pi]
  exact cinterp_cset _

theorem addZero_valid :
    SchemaValid (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN)) =
      (CTm.appSpine (.const addN) [.var 0, .const zeroN] : CTm Tower.Head 1) := by decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  refine SpineFacts.church_root (objectChurch_declared (T := addType) (by decide) rfl)
    objectChurchReading_add_church (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine _
    [cinterp objectChurchReading (σ 0) ρ, objectChurchReading.const zeroN] = _
  rw [objectChurchReading_zero, appSpine_addRaw, Ideal.natRec_zeroI (cont₂_constStep _)]
  rfl

theorem addSuc_valid :
    SchemaValid (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 [.recursive])
        (addBody sucN [.recursive])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN)) =
      (CTm.appSpine (.const addN) [.var 1, .app (.const sucN) (.var 0)] : CTm Tower.Head 2) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive])) =
      (.app (.const sucN) (CTm.appSpine (.const addN) [.var 1, .var 0]) : CTm Tower.Head 2) := by
    decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  have declared := objectChurch_declared (c := addN) (T := addType) (by decide) rfl
  obtain ⟨⟨-, spine⟩, argFacts⟩ := SpineFacts.constSpine declared sl
  have hm :
      projT natI (cinterp objectChurchReading (σ 0) ρ) = cinterp objectChurchReading (σ 0) ρ :=
    SpineFacts.sucArg (argFacts [σ 1] (.app (.const sucN) (σ 0)) [] rfl)
  change SpineTyped (cinterp objectChurchReading (.pi cnum (.pi cnum cnum)) Env.nil)
    [cinterp objectChurchReading (σ 1) ρ, _] at spine
  have ha := ((spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 spine).1
  rw [cinterp_cnum] at ha
  have spineAM : SpineTyped (cinterp objectChurchReading (liftTm addType) Env.nil)
      [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ] :=
    (spineTyped_cinterp_pi objectChurchReading cnum (.pi cnum cnum) Env.nil _ _).2
      ⟨by rw [cinterp_cnum]; exact ha,
        (spineTyped_cinterp_pi objectChurchReading cnum cnum _ _ []).2
          ⟨by rw [cinterp_cnum]; exact hm, trivial⟩⟩
  refine SpineFacts.church_root declared objectChurchReading_add_church (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine _ [cinterp objectChurchReading (σ 1) ρ,
      Ideal.app (objectChurchReading.const sucN) (cinterp objectChurchReading (σ 0) ρ)] =
    Ideal.app (objectChurchReading.const sucN) (Ideal.appSpine (objectChurchReading.const addN)
      [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ])
  rw [objectChurchReading_suc, objectChurchReading_add_church,
    Ideal.appSpine_churchConst _ (churchTele_cinterp objectChurchReading (liftTm addType) Env.nil)
      (Nat.le_refl _) spineAM, instPi_addType, app_suc_projT, appSpine_addRaw, appSpine_addRaw,
    app_sucConst objectChurchReading numNames objectChurchReading_num
      (cinterp objectChurchReading (σ 0) ρ), hm,
    Ideal.natRec_succI (cont₂_constStep _)]

theorem powZero_valid :
    SchemaValid (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN)) =
      (CTm.appSpine (.const powN) [.const zeroN, .var 0] : CTm Tower.Head 1) := by decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  refine SpineFacts.church_root (objectChurch_declared (T := powType) (by decide) rfl)
    objectChurchReading_pow_church (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine _
    [objectChurchReading.const zeroN, cinterp objectChurchReading (σ 0) ρ] = _
  rw [objectChurchReading_zero, appSpine_powRaw, Ideal.natRec_zeroI (cont₂_constStep _)]
  rfl

theorem powSuc_valid :
    SchemaValid (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 [.recursive])
        (powBody sucN [.recursive])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN)) =
      (CTm.appSpine (.const powN) [.app (.const sucN) (.var 1), .var 0] : CTm Tower.Head 2) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 [.recursive]) (powBody sucN [.recursive])) =
      (.app (.const powerN) (CTm.appSpine (.const powN) [.var 1, .var 0]) : CTm Tower.Head 2) := by
    decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  have declared := objectChurch_declared (c := powN) (T := powType) (by decide) rfl
  obtain ⟨⟨-, spine⟩, argFacts⟩ := SpineFacts.constSpine declared sl
  have hn :
      projT natI (cinterp objectChurchReading (σ 1) ρ) = cinterp objectChurchReading (σ 1) ρ :=
    SpineFacts.sucArg (argFacts [] (.app (.const sucN) (σ 1)) [σ 0] rfl)
  change SpineTyped (cinterp objectChurchReading (.pi cnum (.pi cset cset)) Env.nil)
    [_, cinterp objectChurchReading (σ 0) ρ] at spine
  have hx := ((spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1
    ((spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 spine).2).1
  rw [cinterp_cset] at hx
  have spineNX : SpineTyped (cinterp objectChurchReading (liftTm powType) Env.nil)
      [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ] :=
    (spineTyped_cinterp_pi objectChurchReading cnum (.pi cset cset) Env.nil _ _).2
      ⟨by rw [cinterp_cnum]; exact hn,
        (spineTyped_cinterp_pi objectChurchReading cset cset _ _ []).2
          ⟨by rw [cinterp_cset]; exact hx, trivial⟩⟩
  refine SpineFacts.church_root declared objectChurchReading_pow_church (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine _
      [Ideal.app (objectChurchReading.const sucN) (cinterp objectChurchReading (σ 1) ρ),
        cinterp objectChurchReading (σ 0) ρ] =
    Ideal.app (objectChurchReading.const powerN) (Ideal.appSpine (objectChurchReading.const powN)
      [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ])
  rw [objectChurchReading_pow_church,
    Ideal.appSpine_churchConst _ (churchTele_cinterp objectChurchReading (liftTm powType) Env.nil)
      (Nat.le_refl _) spineNX, instPi_powType, app_power_projT, appSpine_powRaw, appSpine_powRaw,
    objectChurchReading_suc,
    app_sucConst objectChurchReading numNames objectChurchReading_num
      (cinterp objectChurchReading (σ 1) ρ), hn,
    Ideal.natRec_succI (cont₂_constStep _)]

/-! ## The iterator -/

theorem iterType_eq :
    (liftTm Package.iterType : CTm Tower.Head 0) = .pi cnum (CTm.rename wk iterTail) := by
  decide

theorem iterStepType_eq :
    pisCtx iterStepTele (.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6) =
      .pi iterTail (CTm.rename wk iterTail) := by
  decide

/-- The iterator's declared type, at a count, is its type at a count. -/
theorem instPi_iterType (ν : Ideal) :
    instPi (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) [ν] =
      cinterp objectChurchReading iterTail Env.nil := by
  rw [iterType_eq, instPi_cinterp_pi]
  exact cinterp_rename_wk objectChurchReading iterTail _ Env.nil

theorem app_iterRaw (ν : Ideal) :
    Ideal.app (iterRaw objectChurchReading) ν =
      natRec (iterZero objectChurchReading)
        (fun _ r => Ideal.app (iterSucc objectChurchReading) r) ν :=
  Ideal.app_lam_principal (Ideal.cont_natRec (cont₂_constStep _)) ν

/-- The iterator at zero pairs the value with its evidence. -/
theorem iterZero_apply {α π s ξ ε : Ideal}
    (spine : SpineTyped (cinterp objectChurchReading iterTail Env.nil) [α, π, s, ξ, ε]) :
    Ideal.appSpine (iterZero objectChurchReading) [α, π, s, ξ, ε] = Ideal.pair ξ ε := by
  unfold iterZero
  rw [appSpine_cinterp_lamsCtx objectChurchReading iterTele _ iterCod _ rfl,
    Ideal.projArgs_of_spineTyped
      (T := cinterp objectChurchReading (pisCtx iterTele iterCod) Env.nil) spine]
  rfl

/-- The iterator's successor step: the step at the value and its evidence, then the
recursive value, projected onto the iterator's type at a count, at the components. -/
theorem iterSucc_apply {rec α π s ξ ε : Ideal}
    (spine : SpineTyped (cinterp objectChurchReading iterTail Env.nil) [α, π, s, ξ, ε]) :
    Ideal.appSpine (iterSucc objectChurchReading) [rec, α, π, s, ξ, ε] =
      Ideal.app (Ideal.clam (Ideal.csigma α fun y => Ideal.app π y) fun pk =>
          Ideal.app (Ideal.app (Ideal.appSpine
            (projT (cinterp objectChurchReading iterTail Env.nil) rec) [α, π, s]) (Ideal.fst pk))
            (Ideal.snd pk))
        (Ideal.app (Ideal.app s ξ) ε) := by
  unfold iterSucc
  rw [appSpine_cinterp_lamsCtx objectChurchReading iterStepTele _
      (.sigma (.var 4) (.app (.var 4) (.var 0))) _ rfl, iterStepType_eq, projArgs_cinterp_pi,
    show cinterp objectChurchReading (CTm.rename wk iterTail)
        (Env.cons (projT (cinterp objectChurchReading iterTail Env.nil) rec) Env.nil) =
      cinterp objectChurchReading iterTail Env.nil from cinterp_rename_wk _ _ _ _,
    Ideal.projArgs_of_spineTyped spine]
  rfl

theorem iterZero_valid :
    SchemaValid (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName)) =
      (CTm.appSpine (.const iterName) [.const zeroN, .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 5) := by decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) =
      (.pair (.var 1) (.var 0) : CTm Tower.Head 5) := by decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  have declared := objectChurch_declared (c := iterName) (T := Package.iterType) (by decide) rfl
  obtain ⟨⟨-, spine⟩, -⟩ := SpineFacts.constSpine declared sl
  change SpineTyped (cinterp objectChurchReading (liftTm Package.iterType) Env.nil)
    ([objectChurchReading.const zeroN] ++
      [cinterp objectChurchReading (σ 4) ρ, cinterp objectChurchReading (σ 3) ρ,
        cinterp objectChurchReading (σ 2) ρ, cinterp objectChurchReading (σ 1) ρ,
        cinterp objectChurchReading (σ 0) ρ]) at spine
  have tail := (Ideal.spineTyped_append.1 spine).2
  rw [instPi_iterType] at tail
  refine SpineFacts.church_root declared objectChurchReading_iter (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine (Ideal.app (iterRaw objectChurchReading) (objectChurchReading.const zeroN))
      [cinterp objectChurchReading (σ 4) ρ, cinterp objectChurchReading (σ 3) ρ,
        cinterp objectChurchReading (σ 2) ρ, cinterp objectChurchReading (σ 1) ρ,
        cinterp objectChurchReading (σ 0) ρ] =
    Ideal.pair (cinterp objectChurchReading (σ 1) ρ) (cinterp objectChurchReading (σ 0) ρ)
  rw [app_iterRaw, objectChurchReading_zero, Ideal.natRec_zeroI (cont₂_constStep _)]
  exact iterZero_apply tail

theorem iterSuc_valid :
    SchemaValid (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) := by
  intro n σ τ ρ sl hr
  have eL : elabLeft objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName)) =
      (CTm.appSpine (.const iterName)
        [.app (.const sucN) (.var 5), .var 4, .var 3, .var 2, .var 1, .var 0] :
        CTm Tower.Head 6) := by decide
  have eR : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) =
      (.app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
          (.app (.app (.app (.app (.app (.app (.const iterName) (.var 6)) (.var 5)) (.var 4))
            (.var 3)) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 2) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by decide
  rw [eL, csubst_appSpine] at sl ⊢
  rw [eR] at hr ⊢
  have declared := objectChurch_declared (c := iterName) (T := Package.iterType) (by decide) rfl
  obtain ⟨⟨-, spine⟩, argFacts⟩ := SpineFacts.constSpine declared sl
  have hν :
      projT natI (cinterp objectChurchReading (σ 5) ρ) = cinterp objectChurchReading (σ 5) ρ :=
    SpineFacts.sucArg (argFacts [] (.app (.const sucN) (σ 5)) [σ 4, σ 3, σ 2, σ 1, σ 0] rfl)
  set ν := cinterp objectChurchReading (σ 5) ρ
  set α := cinterp objectChurchReading (σ 4) ρ
  set π := cinterp objectChurchReading (σ 3) ρ
  set st := cinterp objectChurchReading (σ 2) ρ
  set ξ := cinterp objectChurchReading (σ 1) ρ
  set ε := cinterp objectChurchReading (σ 0) ρ
  change SpineTyped (cinterp objectChurchReading (liftTm Package.iterType) Env.nil)
    ([Ideal.app (objectChurchReading.const sucN) ν] ++ [α, π, st, ξ, ε]) at spine
  have tail := (Ideal.spineTyped_append.1 spine).2
  rw [instPi_iterType] at tail
  have tail3 : SpineTyped (cinterp objectChurchReading iterTail Env.nil) [α, π, st] :=
    (Ideal.spineTyped_append (args := [α, π, st]) (args' := [ξ, ε]) |>.1 tail).1
  have spine4 :
      SpineTyped (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) [ν, α, π, st] := by
    refine Ideal.spineTyped_append (args := [ν]) (args' := [α, π, st]) |>.2 ⟨?_, ?_⟩
    · rw [iterType_eq]
      exact (spineTyped_cinterp_pi objectChurchReading cnum _ Env.nil ν []).2
        ⟨by rw [cinterp_cnum]; exact hν, trivial⟩
    · rw [instPi_iterType]
      exact tail3
  have key : Ideal.appSpine (projT (cinterp objectChurchReading iterTail Env.nil)
      (natRec (iterZero objectChurchReading)
        (fun _ r => Ideal.app (iterSucc objectChurchReading) r) ν))
      [α, π, st] = Ideal.appSpine (objectChurchReading.const iterName) [ν, α, π, st] := by
    rw [objectChurchReading_iter,
      Ideal.appSpine_churchConst _ (churchTele_cinterp objectChurchReading _ Env.nil)
        (by show 4 ≤ 6; omega) spine4,
      Ideal.appSpine_churchConst _ (churchTele_cinterp objectChurchReading iterTail Env.nil)
        (by show 3 ≤ 5; omega) tail3, show [ν, α, π, st] = [ν] ++ [α, π, st] from rfl,
      Ideal.instPi_append, instPi_iterType]
    show _ = projT _ (Ideal.appSpine (Ideal.app (iterRaw objectChurchReading) ν) [α, π, st])
    rw [app_iterRaw]
  refine SpineFacts.church_root declared objectChurchReading_iter (Nat.le_refl _) sl ?_ hr
  change Ideal.appSpine (Ideal.app (iterRaw objectChurchReading)
      (Ideal.app (objectChurchReading.const sucN) ν)) [α, π, st, ξ, ε] =
    cinterp objectChurchReading ((CTm.app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
          (.app (.app (.app (.app (.app (.app (.const iterName) (.var 6)) (.var 5)) (.var 4))
            (.var 3)) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 2) (.var 1)) (.var 0))).subst σ) ρ
  rw [cinterp_subst, app_iterRaw, objectChurchReading_suc,
    app_sucConst objectChurchReading numNames objectChurchReading_num ν, hν,
    Ideal.natRec_succI (cont₂_constStep _)]
  change Ideal.appSpine (iterSucc objectChurchReading) (_ :: [α, π, st, ξ, ε]) = _
  rw [iterSucc_apply tail, key]
  rfl

/-! ## Definitions by one equation -/

/-- **A definition by one equation is valid** when its declared type is the dependent
function type of a codomain over its annotated telescope. -/
theorem def_valid {f : DeclName} {tag : ObjConst} (htag : objConst f = tag) {k : Nat}
    {Θ : Tower.Ctx k} {rhs : Tower.Tm k} {D : Tower.Tm 0} {T : CTm Tower.Head k}
    (hD : objectRules.constantType f = some D) (lf : lamFree D = true)
    (hDT : liftTm D = pisCtx (liftCtx Θ) T) (declType : tag.declType = pisCtx (liftCtx Θ) T)
    (raw : tag.raw objectChurchReading = defRaw objectChurchReading f Θ rhs)
    (args : List (CTm Tower.Head k)) (hlen : args.length = k)
    (hargs : elabLeft objectDecls (applyClosed Θ Presentation.ids (.const f)) =
      CTm.appSpine (.const f) args)
    (henv : ∀ {n : Nat} (σ : CSub Tower.Head k n) (ρ : Env n),
      Env.ofArgs k ((args.map (CTm.subst σ)).map (cinterp objectChurchReading · ρ)) =
        fun i => cinterp objectChurchReading (σ i) ρ) :
    SchemaValid (applyClosed Θ Presentation.ids (.const f)) rhs := by
  intro n σ τ ρ sl hr
  have declared : objectChurch.constantType f = some (pisCtx (liftCtx Θ) T) := by
    rw [← hDT]
    exact objectChurch_declared hD lf
  rw [hargs, csubst_appSpine] at sl ⊢
  rw [cinterp_subst] at hr ⊢
  rw [← henv σ ρ] at hr ⊢
  exact SpineFacts.defConst_root declared (objectChurchReading_def htag declType raw)
    (by rw [List.length_map, hlen]) sl hr

theorem eqAt_valid :
    SchemaValid (applyClosed eqAtTele Presentation.ids (.const eqAtName)) eqAtRhs :=
  def_valid (tag := .eqAt) (by decide) (D := Package.eqAtType) (T := cU0) (by decide) (by decide)
    (by decide) (by decide) rfl [.var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_nil _ _)

theorem sucMove_valid :
    SchemaValid (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName)) sucMoveRhs :=
  def_valid (tag := .sucMove) (by decide) (D := Package.sucMoveType) (T := ceqAt (csuc (.var 1)))
    (by decide) (by decide) (by decide) (by decide) rfl [.var 1, .var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_nil _ _))

theorem keep_valid :
    SchemaValid (applyClosed keepTele Presentation.ids (.const keepName)) keepRhs :=
  def_valid (tag := .keep) (by decide) (D := Package.keepType)
    (T := .sigma (.var 3) (.app (.var 3) (.var 0))) (by decide) (by decide) (by decide) (by decide)
    rfl [.var 3, .var 2, .var 1, .var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl
      (Env.eq_nil _ _))))

theorem transport_valid :
    SchemaValid (applyClosed transportTelescope Presentation.ids (.const transportName))
      transportRhs :=
  def_valid (tag := .transport) (by decide) (D := Package.transportType)
    (T := .sigma (.var 5) (.app (.var 5) (.var 0))) (by decide) (by decide) (by decide) (by decide)
    rfl [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl
      (Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_nil _ _))))))

theorem compose_valid :
    SchemaValid (applyClosed composeTelescope Presentation.ids (.const composeName)) composeRhs :=
  def_valid (tag := .compose) (by decide) (D := Package.composeType)
    (T := .sigma (.var 5) (.app (.var 5) (.var 0))) (by decide) (by decide) (by decide) (by decide)
    rfl [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_cons rfl
      (Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_nil _ _))))))

/-- The codomain of `returnIter` after its carrier. -/
abbrev returnIterCod : CTm Tower.Head 1 :=
  .pi (.pi (.var 0) cU0) (.pi cnum (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
    (.sigma (.var 4) (.app (.var 4) (.var 0))))) (.pi (.var 3) (.pi (.app (.var 3) (.var 0))
      (.sigma (.var 5) (.app (.var 5) (.var 0)))))))

theorem returnIter_valid :
    SchemaValid (applyClosed returnIterTele Presentation.ids (.const returnIterName))
      returnIterRhs :=
  def_valid (tag := .returnIter) (by decide) (D := Package.returnIterType) (T := returnIterCod)
    (by decide) (by decide) (by decide) (by decide) rfl [.var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_nil _ _)

theorem sucStep_valid :
    SchemaValid (applyClosed eqAtTelescope Presentation.ids (.const sucStepName)) sucStepRhs :=
  def_valid (tag := .sucStep) (by decide) (D := Package.sucStepType)
    (T := .sigma cnum (ceqAt (.var 0))) (by decide) (by decide) (by decide) (by decide) rfl
    [.var 1, .var 0] rfl (by decide)
    fun _ _ => Env.eq_cons rfl (Env.eq_cons rfl (Env.eq_nil _ _))

/-! ## Decoding -/

theorem imp_valid :
    SchemaValid (k := 2) (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)))
      (.pi (.app (.const holdsN) (.var 1))
        (.app (.const holdsN) (Presentation.rename wk (.var 0)))) := by
  intro n σ τ ρ _ _
  have eL : elabLeft objectDecls
      (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)) : Tower.Tm 2) =
      .app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)) := by decide
  have eR : elabRight objectDecls
      (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)) : Tower.Tm 2)
      (.pi (.app (.const holdsN) (.var 1))
        (.app (.const holdsN) (Presentation.rename wk (.var 0)))) =
      (.pi (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (.var 1)) : CTm Tower.Head 2) := by
    decide
  rw [eL, eR, cinterp_subst, cinterp_subst]
  change Ideal.app (objectChurchReading.const holdsN)
      (Ideal.appSpine (objectChurchReading.const impN)
        [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ]) =
    cpi (Ideal.app (objectChurchReading.const holdsN) (cinterp objectChurchReading (σ 1) ρ))
      fun _ => Ideal.app (objectChurchReading.const holdsN) (cinterp objectChurchReading (σ 0) ρ)
  rw [objectChurchReading_holds, objectChurchReading_imp]
  exact Ideal.decode_impConst _ _

theorem all_valid (type : HOL.Ty SetProfile.SetBase) :
    SchemaValid (k := 1) (.app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0)))
      (.pi (Presentation.liftClosed (typeTerm type))
        (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) := by
  intro n σ τ ρ _ _
  have lf : lamFree ((Tm.pi (Presentation.liftClosed (typeTerm type))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) : Tower.Tm 1) =
      true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Presentation.rename,
      Bool.and_self]
  rw [elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0)) : Tower.Tm 1) =
        true),
    elabRight, elab_lamFree _ lf, cinterp_subst, cinterp_subst]
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 1) =
      liftTm (typeAt SetProfile.types 1 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  change Ideal.app (objectChurchReading.const holdsN)
      (Ideal.app (objectChurchReading.const (SetProfile.allName type))
        (cinterp objectChurchReading (σ 0) ρ)) =
    cpi (cinterp objectChurchReading (liftTm (Presentation.liftClosed (typeTerm type)))
      fun i => cinterp objectChurchReading (σ i) ρ) fun y =>
      Ideal.app (objectChurchReading.const holdsN)
        (Ideal.app (cinterp objectChurchReading (σ 0) ρ) y)
  rw [objectChurchReading_holds, objectChurchReading_all, hA, cinterp_objectTypeAt]
  exact Ideal.decode_allConst (typeGenerated_simpleI type) _

theorem eq_valid (type : HOL.Ty SetProfile.SetBase) :
    SchemaValid (k := 2)
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)))
      (.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0)) := by
  intro n σ τ ρ sl hr
  have lf : lamFree ((Tm.id (Presentation.liftClosed (typeTerm type)) (.var 1) (.var 0)) :
      Tower.Tm 2) = true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Bool.and_self]
  have fo : firstOrder (.app (.const holdsN)
      (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)) : Tower.Tm 2) = true := rfl
  rw [elabLeft_firstOrder objectDecls fo] at sl ⊢
  rw [elabRight, elab_lamFree _ lf] at hr ⊢
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 2) =
      liftTm (typeAt SetProfile.types 2 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  -- the left side's type is the universe
  obtain ⟨⟨inst, -⟩, -⟩ := SpineFacts.constSpine (args := [(.app (.app
    (.const (SetProfile.eqName type)) (.var 1)) (.var 0) : CTm Tower.Head 2).subst σ])
    (objectChurch_declared (c := holdsN) (T := programCodes.holdsType) (by decide) rfl) sl
  have hτ : τ = univIdeal := by
    rw [← inst]
    show instPi
      (cinterp objectChurchReading (.pi (.const propN) (.head (.sort Tower.zero))) Env.nil) _ = _
    rw [List.map_cons, List.map_nil, instPi_cinterp_pi]
    rfl
  rw [cinterp_subst] at hr ⊢
  rw [cinterp_subst]
  rw [hτ] at hr
  change projT univIdeal (Ideal.ident (cinterp objectChurchReading
      (liftTm (Presentation.liftClosed (typeTerm type)))
      fun i => cinterp objectChurchReading (σ i) ρ)
      (cinterp objectChurchReading (σ 1) ρ) (cinterp objectChurchReading (σ 0) ρ)) =
    Ideal.ident (cinterp objectChurchReading
      (liftTm (Presentation.liftClosed (typeTerm type)))
      fun i => cinterp objectChurchReading (σ i) ρ)
      (cinterp objectChurchReading (σ 1) ρ) (cinterp objectChurchReading (σ 0) ρ) at hr
  change Ideal.app (objectChurchReading.const holdsN) (Ideal.appSpine
      (objectChurchReading.const (SetProfile.eqName type))
      [cinterp objectChurchReading (σ 1) ρ, cinterp objectChurchReading (σ 0) ρ]) =
    Ideal.ident (cinterp objectChurchReading (liftTm (Presentation.liftClosed (typeTerm type)))
      fun i => cinterp objectChurchReading (σ i) ρ) (cinterp objectChurchReading (σ 1) ρ)
      (cinterp objectChurchReading (σ 0) ρ)
  rw [hA, cinterp_objectTypeAt] at hr ⊢
  rw [objectChurchReading_holds, objectChurchReading_eq]
  exact Ideal.decode_eqConst hr

/-! ## Every schema -/

/-- **Every rewrite schema of the object package is valid in the object reading.** -/
theorem objectSchemas_valid {k : Nat} {L R : Tm Tower.Head k} (rule : objectSchemas L R) :
    SchemaValid L R := by
  rcases rule with rule | rule
  · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
    simp only [computationSpecs, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, k', fields, hi, rule⟩ := rule
      rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact numRecZero_valid
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact numRecSuc_valid
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hi
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact addZero_valid
      · exact addSuc_valid
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact powZero_valid
      · exact powSuc_valid
    · cases rule
      exact j_valid
    · cases rule
      exact eqAt_valid
    · cases rule
      exact sucMove_valid
    · cases rule
      exact keep_valid
    · cases rule
      exact transport_valid
    · cases rule
      exact compose_valid
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact iterZero_valid
      · exact iterSuc_valid
    · cases rule
      exact returnIter_valid
    · cases rule
      exact sucStep_valid
  · rcases rule with rule | ⟨a, A, carrier, rule⟩ | ⟨e, A, carrier, rule⟩
    · cases rule
      exact imp_valid
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.allInstance?_eq_some found
          cases rule
          exact all_valid type
    · change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
        at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? e with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.eqInstance?_eq_some found
          cases rule
          exact eq_valid type

/-! ## Validity and soundness -/

/-- **The root steps of the object package's annotation are valid in the object reading.** -/
theorem objectChurchReading_roots {n : Nat} {l r : CTm Tower.Head n} {τ : Ideal} {ρ : Env n}
    (step : objectChurch.computation.step l r) (_ : TypeGenerated τ)
    (_ : projT τ (cinterp objectChurchReading l ρ) = cinterp objectChurchReading l ρ)
    (facts : SpineFacts objectChurchReading objectChurch l τ ρ)
    (right : projT τ (cinterp objectChurchReading r ρ) = cinterp objectChurchReading r ρ)
    (_ : SpineFacts objectChurchReading objectChurch r τ ρ) :
    cinterp objectChurchReading l ρ = cinterp objectChurchReading r ρ := by
  cases step with
  | instantiate rule σ =>
      obtain ⟨L, R, hS, rfl, rfl⟩ := rule
      exact objectSchemas_valid hS σ facts right

/-- **The object reading validates the object package's annotation.** -/
theorem objectChurchReading_valid : ReadingValid objectChurchReading objectChurch :=
  ReadingValid.ofLevels ConvRules.objectLevels
    (fun {h} hu => by cases hu; rfl)
    (fun h => by
      cases h with
      | sort _ => exact Elem.ty_univ_univ
      | legacyGround => exact Elem.ty_tag (k := .ground) trivial Elem.isUniv_univ)
    (fun {h h'} same => by
      cases h <;> cases h' <;> first | rfl | exact same.elim)
    (fun declared _ => objectChurchReading_constants declared)
    objectChurchReading_roots

/-- **Soundness of the object package's annotation**: every derivable statement holds in the
domain under the object reading. -/
theorem objectChurch_sound {J : CStatement Tower.Head} (derivation : CDerivable objectChurch J) :
    J.Sound objectChurchReading objectChurch :=
  CDerivable.sound objectChurchReading_valid derivation

/-- **The soundness facts** of the relation's compatibility lemmas, at the object package. -/
theorem objectChurch_soundnessFacts : SoundnessFacts objectChurchReading objectChurch :=
  objectChurchReading_valid.soundnessFacts

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
