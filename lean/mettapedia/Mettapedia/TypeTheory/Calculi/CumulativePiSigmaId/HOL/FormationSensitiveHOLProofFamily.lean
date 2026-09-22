import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation

/-!
# Native proof families for the uniform HOL declaration interface

The existing proposition carrier is extended with an opaque decoder `Prf`.
Two declaration equations decode implication and universal quantification as
native dependent products. The equations are closed under capture-avoiding
renaming and substitution, and their endpoints are formed whenever their HOL
operands are formed. Existing declarations and derivations are preserved by an
actual rules morphism.

This constructs a syntactic candidate interface, not a model or a consistency
theorem for the entire extended calculus. In particular, no equation decodes
HOL equality as native identity, and no new equality or choice principle is
installed. The semantic interpretation of this extension is a separate task.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofFamily

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic

namespace Source
export FormationSensitiveHOLUniformList (types rawImp universal)
end Source

def proofName : DeclName := `HOLUniformList.Prf

def proofType : Tower.Tm 0 :=
  .pi (.const `HOLUniformList.prop) (sortTm Tower.zero)

def proof {n : Nat} (proposition : Tower.Tm n) : Tower.Tm n :=
  .app (.const proofName) proposition

def implicationFamily {n : Nat} (p q : Tower.Tm n) : Tower.Tm n :=
  .pi (proof p) (Presentation.rename wk (proof q))

def universalProposition {n : Nat} (a f : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const `HOLUniformList.universal) a) f

def universalFamily {n : Nat} (a f : Tower.Tm n) : Tower.Tm n :=
  .pi a (proof (.app (Presentation.rename wk f) (.var 0)))

@[simp] theorem proof_rename {n m : Nat} (rho : Ren n m) (p : Tower.Tm n) :
    Presentation.rename rho (proof p) = proof (Presentation.rename rho p) := rfl

@[simp] theorem proof_subst {n m : Nat} (sigma : Sub Tower.Head n m) (p : Tower.Tm n) :
    Presentation.subst sigma (proof p) = proof (Presentation.subst sigma p) := rfl

@[simp] theorem implicationFamily_rename {n m : Nat} (rho : Ren n m) (p q : Tower.Tm n) :
    Presentation.rename rho (implicationFamily p q) =
      implicationFamily (Presentation.rename rho p) (Presentation.rename rho q) := by
  simp [implicationFamily, Presentation.rename, rename_comp, liftRen, wk, proof]

@[simp] theorem implicationFamily_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (p q : Tower.Tm n) :
    Presentation.subst sigma (implicationFamily p q) =
      implicationFamily (Presentation.subst sigma p) (Presentation.subst sigma q) := by
  simp [implicationFamily, proof, Presentation.subst, Presentation.rename,
    subst_rename, rename_subst, liftSub, wk]

@[simp] theorem universalFamily_rename {n m : Nat} (rho : Ren n m) (a f : Tower.Tm n) :
    Presentation.rename rho (universalFamily a f) =
      universalFamily (Presentation.rename rho a) (Presentation.rename rho f) := by
  simp [universalFamily, Presentation.rename, rename_comp, liftRen, wk, proof]

@[simp] theorem universalFamily_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (a f : Tower.Tm n) :
    Presentation.subst sigma (universalFamily a f) =
      universalFamily (Presentation.subst sigma a) (Presentation.subst sigma f) := by
  simp [universalFamily, Presentation.subst, subst_rename, rename_subst, liftSub, wk, proof]

/-- Exactly the two proof-family equations, at arbitrary binding depth. -/
inductive DecoderStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | implication {n : Nat} (p q : Tower.Tm n) :
      DecoderStep (proof (Source.rawImp p q)) (implicationFamily p q)
  | universal {n : Nat} (a f : Tower.Tm n) :
      DecoderStep (proof (universalProposition a f)) (universalFamily a f)

def computation : RootComputation Tower.Head where
  step := DecoderStep
  rename := by
    intro n m rho left right step
    cases step with
    | implication p q =>
        simpa only [proof_rename, implicationFamily_rename,
          FormationSensitiveHOLUniformList.rawImp, Presentation.rename] using
          DecoderStep.implication (Presentation.rename rho p) (Presentation.rename rho q)
    | universal a f =>
        simpa only [proof_rename, universalFamily_rename, universalProposition,
          Presentation.rename] using
          DecoderStep.universal (Presentation.rename rho a) (Presentation.rename rho f)
  substitute := by
    intro n m sigma left right step
    cases step with
    | implication p q =>
        simpa only [proof_subst, implicationFamily_subst,
          FormationSensitiveHOLUniformList.rawImp, Presentation.subst] using
          DecoderStep.implication (Presentation.subst sigma p) (Presentation.subst sigma q)
    | universal a f =>
        simpa only [proof_subst, universalFamily_subst, universalProposition,
          Presentation.subst] using
          DecoderStep.universal (Presentation.subst sigma a) (Presentation.subst sigma f)

def declarations : Signature Tower.Head where
  entries := (FormationSensitiveHOLUniformList.declarations.insert proofName
    ⟨proofType, none⟩).entries
  computation := computation

def rules : Rules Tower.Head := extendRules Tower.rules declarations

theorem proofName_fresh :
    FormationSensitiveHOLUniformList.declarations.entries proofName = none := by decide

theorem extends_source : FormationSensitiveHOLUniformList.declarations.Extends declarations where
  entries := by
    intro name entry known
    by_cases equal : name = proofName
    · subst name
      rw [proofName_fresh] at known
      cases known
    · simpa [declarations, Signature.insert, equal] using known
  computation := by
    intro n left right step
    exact step.elim

theorem sourceMorphism : FormationSensitiveHOLUniformList.rules.Morphism rules (fun head => head) :=
  extensionMorphism Tower.rules extends_source

theorem include_typed {n : Nat} {gamma : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing FormationSensitiveHOLUniformList.rules gamma term type) :
    Typing rules gamma term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead sourceMorphism

theorem include_context {n : Nat} {gamma : Tower.Ctx n}
    (formed : ContextFormation FormationSensitiveHOLUniformList.rules gamma) :
    ContextFormation rules gamma := by
  simpa only [Ctx.mapHead_id] using formed.mapHead sourceMorphism

theorem proposition_formed {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  include_typed (FormationSensitiveHOLUniformList.proposition_formed gamma)

theorem simple_type_formed (type : HOL.Ty HOL.UniformListInduction.BaseSort)
    {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (typeAt Source.types n type) (sortTm Tower.zero) :=
  include_typed (FormationSensitiveHOLUniformList.simple_type_formed type gamma)

theorem proofType_formed : Typing rules .nil proofType
    (sortTm (.max Tower.zero (.succ Tower.zero))) :=
  .piForm (proposition_formed .nil) (.sort Tower.zero)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    (.sorts Tower.zero (.succ Tower.zero))

theorem proofConstant_typed {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (.const proofName) (liftClosed proofType) :=
  .const (by decide) proofType_formed (.sort (.max Tower.zero (.succ Tower.zero)))

theorem proof_formed {n : Nat} {gamma : Tower.Ctx n} {p : Tower.Tm n}
    (typed : Typing rules gamma p (.const `HOLUniformList.prop)) :
    Typing rules gamma (proof p) (sortTm Tower.zero) := by
  have applied := Typing.appElim (proofConstant_typed gamma) typed
  simpa only [proofType, proof, sortTm, liftClosed, Presentation.rename, inst0,
    Presentation.subst] using applied

theorem pi_zero {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing rules gamma a (sortTm Tower.zero))
    (codomain : Typing rules (.snoc gamma a) b (sortTm Tower.zero)) :
    Typing rules gamma (.pi a b) (sortTm Tower.zero) := by
  apply Typing.cumul (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

theorem implication_proposition {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing rules gamma p (.const `HOLUniformList.prop))
    (hq : Typing rules gamma q (.const `HOLUniformList.prop)) :
    Typing rules gamma (Source.rawImp p q) (.const `HOLUniformList.prop) := by
  have symbol := include_typed
    (closed_typed FormationSensitiveHOLUniformList.signature.implication_typed gamma)
  have first := Typing.appElim symbol hp
  have second := Typing.appElim first hq
  simpa only [Source.rawImp, FormationSensitiveHOLUniformList.signature,
    FormationSensitiveHOLUniformList.types, typeAt, liftClosed, Presentation.rename,
    inst0, Presentation.subst] using second

theorem implication_formed {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing rules gamma p (.const `HOLUniformList.prop))
    (hq : Typing rules gamma q (.const `HOLUniformList.prop)) :
    Typing rules gamma (implicationFamily p q) (sortTm Tower.zero) :=
  pi_zero (proof_formed hp) ((proof_formed hq).weaken)

theorem implication_conversion {n : Nat} (p q : Tower.Tm n) :
    Conv rules.headEq (proof (Source.rawImp p q)) (implicationFamily p q) rules.computation :=
  .rel _ _ (.root (.declared (.implication p q)))

/-- A small-domain predicate applied to its bound variable remains a HOL proposition. -/
theorem predicate_at_variable {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (hf : Typing rules gamma f (.pi a (.const `HOLUniformList.prop))) :
    Typing rules (.snoc gamma a) (.app (Presentation.rename wk f) (.var 0))
      (.const `HOLUniformList.prop) := by
  have applied := Typing.appElim (hf.weaken (extension := a)) (Typing.var 0)
  simpa only [Presentation.rename, inst0, Presentation.subst] using applied

theorem universal_formed {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hf : Typing rules gamma f (.pi a (.const `HOLUniformList.prop))) :
    Typing rules gamma (universalFamily a f) (sortTm Tower.zero) :=
  pi_zero ha (proof_formed (predicate_at_variable hf))

theorem universal_proposition {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hf : Typing rules gamma f (.pi a (.const `HOLUniformList.prop))) :
    Typing rules gamma (universalProposition a f) (.const `HOLUniformList.prop) := by
  have symbol : Typing rules gamma (.const `HOLUniformList.universal)
      (liftClosed FormationSensitiveHOLUniformList.universalType) :=
    include_typed (.const (by decide) FormationSensitiveHOLUniformList.universal_type_formed
      (.sort (.max (.succ Tower.zero) Tower.zero)))
  have applied := Typing.appElim symbol ha
  have first : Typing rules gamma (.app (.const `HOLUniformList.universal) a)
      (.pi (.pi a (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop)) := by
    simpa only [FormationSensitiveHOLUniformList.universalType, liftClosed,
      Presentation.rename, inst0, Presentation.subst, subst0, consSub, liftSub,
      liftRen, Fin.cases_zero] using applied
  have second := Typing.appElim first hf
  simpa only [universalProposition, inst0, Presentation.subst] using second

theorem universal_conversion {n : Nat} (a f : Tower.Tm n) :
    Conv rules.headEq (proof (universalProposition a f)) (universalFamily a f)
      rules.computation :=
  .rel _ _ (.root (.declared (.universal a f)))

/-- Decoding does not substitute for proof construction: implication introduction
is the native lambda constructor, checked against the decoded product. -/
theorem implication_intro {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (hp : Typing rules gamma p (.const `HOLUniformList.prop))
    (hq : Typing rules gamma q (.const `HOLUniformList.prop))
    (hb : Typing rules (.snoc gamma (proof p)) body (Presentation.rename wk (proof q))) :
    Typing rules gamma (.lam body) (proof (Source.rawImp p q)) :=
  .conv (.lamIntro (implication_formed hp hq) (.sort Tower.zero) hb)
    (proof_formed (implication_proposition hp hq)) (.sort Tower.zero)
    (.symm _ _ (implication_conversion p q))

theorem implication_elim {n : Nat} {gamma : Tower.Ctx n} {p q major minor : Tower.Tm n}
    (hp : Typing rules gamma p (.const `HOLUniformList.prop))
    (hq : Typing rules gamma q (.const `HOLUniformList.prop))
    (hm : Typing rules gamma major (proof (Source.rawImp p q)))
    (ha : Typing rules gamma minor (proof p)) :
    Typing rules gamma (.app major minor) (proof q) := by
  have converted := Typing.conv hm (implication_formed hp hq) (.sort Tower.zero)
    (implication_conversion p q)
  simpa only [implicationFamily, inst0_rename_wk] using Typing.appElim converted ha

private theorem instantiate_shifted_body {n : Nat} (body : Tower.Tm (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) body) = body := by
  unfold inst0
  rw [subst_rename]
  calc
    Presentation.subst (fun index => subst0 (.var 0) (liftRen wk index)) body =
        Presentation.subst ids body := by
      apply subst_ext
      intro index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro prior
        rfl
    _ = body := subst_ids body

/-- The authored universal is application to a lambda. Its decoder equation
followed by native beta computes to the actual dependent proof family. -/
theorem universal_lambda_conversion {n : Nat} (a : Tower.Tm n)
    (body : Tower.Tm (n + 1)) :
    Conv rules.headEq (proof (universalProposition a (.lam body)))
      (.pi a (proof body)) rules.computation := by
  refine .trans _ _ _ (universal_conversion a (.lam body)) ?_
  apply Conv.congPi (.refl _)
  apply Conv.congApp (.refl _)
  change Conv rules.headEq (.app (.lam (Presentation.rename (liftRen wk) body)) (.var 0))
    body rules.computation
  simpa only [instantiate_shifted_body] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation)
      (headEq := rules.headEq) (Presentation.rename (liftRen wk) body) (.var 0)))

theorem rawAll_conversion {n : Nat} (type : HOL.Ty HOL.UniformListInduction.BaseSort)
    (body : Tower.Tm (n + 1)) :
    Conv rules.headEq (proof (FormationSensitiveHOLUniformList.rawAll type body))
      (.pi (typeAt Source.types n type) (proof body)) rules.computation := by
  simpa only [FormationSensitiveHOLUniformList.rawAll,
    FormationSensitiveHOLUniformList.universal, universalProposition, liftClosed,
    Presentation.rename, typeAt_rename] using
    universal_lambda_conversion (typeAt Source.types n type) body

theorem universal_lambda_proposition {n : Nat} {gamma : Tower.Ctx n} {a : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hb : Typing rules (.snoc gamma a) body (.const `HOLUniformList.prop)) :
    Typing rules gamma (universalProposition a (.lam body)) (.const `HOLUniformList.prop) :=
  universal_proposition ha
    (.lamIntro (pi_zero ha (proposition_formed _)) (.sort Tower.zero) hb)

theorem universal_intro {n : Nat} {gamma : Tower.Ctx n} {a : Tower.Tm n}
    {p body : Tower.Tm (n + 1)}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hp : Typing rules (.snoc gamma a) p (.const `HOLUniformList.prop))
    (hb : Typing rules (.snoc gamma a) body (proof p)) :
    Typing rules gamma (.lam body) (proof (universalProposition a (.lam p))) :=
  .conv (.lamIntro (pi_zero ha (proof_formed hp)) (.sort Tower.zero) hb)
    (proof_formed (universal_lambda_proposition ha hp)) (.sort Tower.zero)
    (.symm _ _ (universal_lambda_conversion a p))

theorem universal_elim {n : Nat} {gamma : Tower.Ctx n} {a major argument : Tower.Tm n}
    {p : Tower.Tm (n + 1)}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hp : Typing rules (.snoc gamma a) p (.const `HOLUniformList.prop))
    (hm : Typing rules gamma major (proof (universalProposition a (.lam p))))
    (ht : Typing rules gamma argument a) :
    Typing rules gamma (.app major argument) (proof (inst0 argument p)) := by
  have converted := Typing.conv hm (pi_zero ha (proof_formed hp)) (.sort Tower.zero)
    (universal_lambda_conversion a p)
  simpa only [inst0, proof_subst] using Typing.appElim converted ht

/-- The two decoder equations are selective: a bare proposition variable
does not have a decoder-root step. This is not a claim about its whole
conversion class. -/
theorem variable_has_no_decoder_step {n : Nat} (index : Fin n) (result : Tower.Tm n) :
    ¬ DecoderStep (proof (.var index)) result := by
  intro step
  cases step

theorem equality_has_no_decoder_step {n : Nat}
    (type : HOL.Ty HOL.UniformListInduction.BaseSort) (left right result : Tower.Tm n) :
    ¬ DecoderStep (proof (FormationSensitiveHOLUniformList.rawEq type left right)) result := by
  intro step
  cases step

#print axioms extends_source
#print axioms include_typed
#print axioms proof_formed
#print axioms implication_formed
#print axioms universal_formed
#print axioms implication_intro
#print axioms implication_elim
#print axioms universal_intro
#print axioms universal_elim
#print axioms rawAll_conversion
#print axioms variable_has_no_decoder_step
#print axioms equality_has_no_decoder_step

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofFamily
