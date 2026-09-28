import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Evaluation

/-!
# Identity transport through the declared substitution

The source document declares substitution over predicates into `prop`:
`subst@num : ∀ P : num → prop. ∀ x y. x = y → P x → P y`.  Its instance at the
predicate `λ z. add zero i = z` and the points `add zero i` and `i` moves a
proof of `add zero i = add zero i` along `add zero i = i`.  Under the identity
reading the proof family at a represented equation computes to the identity
type, so this instance is an identity-valued transport

  `Π i : num. Holds (add zero i = i) → Id num (add zero i) (add zero i) → Id num (add zero i) i`.

It is built from any evidence for the declared proposition: from the assumption
constant, or from its realization by identity elimination.  Linking replaces
the first by the second.

At an open index `k`, the transport applied to the translated source proof of
`zero-add` at `k` and to `refl (add zero k)` is identity evidence at `k`, and it
feeds the program's successor step there.  Reflexivity cannot take the place of
the source proof at an open index.  At every numeral `m` the linked term runs
to `refl m`, and every run of it that stops, stops there.

Outside the identity reading, a represented equation is not an identity type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.HostedTransport

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Normal instanceOf)
open SetProfile (numTy holdsName zeroNative sucNative addNative eqNumNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Execution
open CertifiedTransformProgram.Confluence (linearRules linearEquations linearConstructors
  implicationLeft universalLeft LinearSchema)
open CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open CertifiedTransformProgram.IdentityEquality.Translation
open CertifiedTransformProgram.IdentityEquality.Evaluation (runs_substitute linkedZeroAdd_runs
  runs_toIdentity refl_numeral_normal)
open FormationSensitiveHOLIdentityEquality (IdentityStep decodes)
open Mettapedia.Logic

/-! ## Represented equations under the identity reading -/

/-- The proof family at `l = r` is `Id num l r` under the identity reading: one
decoding step. -/
theorem holdsEq_identity {n : Nat} (left right : Tower.Tm n) :
    Conv identityRules.headEq (Holds (eqNumNative left right)) (.id numT left right)
      identityRules.computation :=
  .rel _ _ (.root (identity_decodes (IdentityStep.equation numTy left right)))

/-! ## The instance of substitution -/

/-- The predicate `λ z. add zero i = z` at an index `i`. -/
def predicateAt {n : Nat} (index : Tower.Tm n) : Tower.Tm n :=
  .lam (eqNumNative (addNative zeroNative (rename wk index)) (.var 0))

theorem predicateAt_typed {n : Nat} {Γ : Tower.Ctx n} {index : Tower.Tm n}
    (typed : Typing R Γ index numT) : Typing R Γ (predicateAt index) (.pi numT propT) :=
  Typing.lamIntro (pi_at numT_typed propT_typed) (isUniverseAt Tower.zero)
    (eqNum_typed (addNative_typed zeroNative_typed (typed.weaken (extension := numT)))
      (Typing.var 0))

/-- Substitution evidence `s` at the predicate `λ z. add zero i = z` and the
points `add zero i` and `i`: `λ i e r. s (λ z. add zero i = z) (add zero i) i e r`. -/
def transportThrough (substitution : Tower.Tm 0) : Tower.Tm 0 :=
  .lam (.lam (.lam (.app (app4 (liftClosed substitution) (predicateAt (.var 2))
    (addNative zeroNative (.var 2)) (.var 2) (.var 1)) (.var 0))))

/-- `Π i : num. Holds (add zero i = i) → Id num (add zero i) (add zero i) → Id num (add zero i) i`. -/
def identityTransportType : Tower.Tm 0 :=
  .pi numT (.pi (Holds (eqNumNative (addNative zeroNative (.var 0)) (.var 0)))
    (.pi (.id numT (addNative zeroNative (.var 1)) (addNative zeroNative (.var 1)))
      (.id numT (addNative zeroNative (.var 2)) (.var 2))))

/-- The contexts `i`, `i e` and `i e r` of the transport. -/
abbrev indexContext : Tower.Ctx 1 := .snoc .nil numT
abbrev hostedContext : Tower.Ctx 2 :=
  .snoc indexContext (Holds (eqNumNative (addNative zeroNative (.var 0)) (.var 0)))
abbrev transportContext : Tower.Ctx 3 :=
  .snoc hostedContext (.id numT (addNative zeroNative (.var 1)) (addNative zeroNative (.var 1)))

theorem substDecoded_formed : Typing R .nil substDecoded U0 := by
  have formed₅ : Typing R (.snoc (.snoc (.snoc (.snoc .nil (.pi numT propT)) numT) numT)
      (.id numT (.var 1) (.var 0)))
      (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2)))) U0 :=
    pi_at (proof_typed (Typing.appElim (B := propT) (Typing.var 3) (Typing.var 2)))
      (proof_typed (Typing.appElim (B := propT) (Typing.var 4) (Typing.var 2)))
  exact pi_at (pi_at numT_typed propT_typed) (pi_at numT_typed (pi_at numT_typed
    (pi_at (id_at numT_typed (Typing.var 1) (Typing.var 0)) formed₅)))

/-- Evidence for the declared substitution has its dependent reading as a type. -/
theorem substEvidence_decoded {substitution : Tower.Tm 0}
    (typed : Typing identityRules .nil substitution (Holds SetProfile.substCode)) :
    Typing identityRules .nil substitution substDecoded :=
  Typing.conv typed (toIdentity substDecoded_formed) (isUniverseAt Tower.zero)
    (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity identity_decodes
      SetProfile.substAxiom rfl substAxiom_decoded))

/-- The instance of any evidence for the declared substitution is an
identity-valued transport under the identity reading. -/
theorem transportThrough_typed {substitution : Tower.Tm 0}
    (typed : Typing identityRules .nil substitution (Holds SetProfile.substCode)) :
    Typing identityRules .nil (transportThrough substitution) identityTransportType := by
  have index : Typing R transportContext (.var 2) numT := Typing.var 2
  have point : Typing R transportContext (addNative zeroNative (.var 2)) numT :=
    addNative_typed zeroNative_typed index
  have hosted : Typing identityRules transportContext (.var 1)
      (Holds (eqNumNative (addNative zeroNative (.var 2)) (.var 2))) := Typing.var 1
  have premise : Typing identityRules transportContext (.var 0)
      (.id numT (addNative zeroNative (.var 2)) (addNative zeroNative (.var 2))) := Typing.var 0
  have substitutionHere := FormationSensitiveHOLInterface.closed_typed
    (substEvidence_decoded typed) transportContext
  have atPredicate := Typing.appElim substitutionHere (toIdentity (predicateAt_typed index))
  have atPoint := Typing.appElim atPredicate (toIdentity point)
  have atEndpoint := Typing.appElim atPoint (toIdentity index)
  -- the hosted equation is the path
  have path : Typing identityRules transportContext (.var 1)
      (.id numT (addNative zeroNative (.var 2)) (.var 2)) :=
    Typing.conv hosted (toIdentity (id_at numT_typed point index)) (isUniverseAt Tower.zero)
      (holdsEq_identity _ _)
  have atPath := Typing.appElim atEndpoint path
  -- `refl (add zero i)` proves the predicate at the point
  have method : Typing identityRules transportContext (.var 0)
      (Holds (.app (predicateAt (.var 2)) (addNative zeroNative (.var 2)))) :=
    Typing.conv premise
      (toIdentity (proof_typed (Typing.appElim (B := propT) (predicateAt_typed index) point)))
      (isUniverseAt Tower.zero)
      (.symm _ _ (.trans _ _ _ (.rel _ _ (.congAppArg (.betaPi _ _))) (holdsEq_identity _ _)))
  have transported : Typing identityRules transportContext
      (.app (app4 (liftClosed substitution) (predicateAt (.var 2))
        (addNative zeroNative (.var 2)) (.var 2) (.var 1)) (.var 0))
      (Holds (.app (predicateAt (.var 2)) (.var 2))) :=
    Typing.appElim atPath method
  -- the predicate at the endpoint is the identity type
  have body : Typing identityRules transportContext
      (.app (app4 (liftClosed substitution) (predicateAt (.var 2))
        (addNative zeroNative (.var 2)) (.var 2) (.var 1)) (.var 0))
      (.id numT (addNative zeroNative (.var 2)) (.var 2)) :=
    Typing.conv transported (toIdentity (id_at numT_typed point index)) (isUniverseAt Tower.zero)
      (.trans _ _ _ (.rel _ _ (.congAppArg (.betaPi _ _))) (holdsEq_identity _ _))
  have formed₃ : Typing R hostedContext
      (.pi (.id numT (addNative zeroNative (.var 1)) (addNative zeroNative (.var 1)))
        (.id numT (addNative zeroNative (.var 2)) (.var 2))) U0 :=
    pi_at (id_at numT_typed (addNative_typed zeroNative_typed (Typing.var 1))
        (addNative_typed zeroNative_typed (Typing.var 1)))
      (id_at numT_typed point index)
  have formed₂ : Typing R indexContext
      (.pi (Holds (eqNumNative (addNative zeroNative (.var 0)) (.var 0)))
        (.pi (.id numT (addNative zeroNative (.var 1)) (addNative zeroNative (.var 1)))
          (.id numT (addNative zeroNative (.var 2)) (.var 2)))) U0 :=
    pi_at (proof_typed (eqNum_typed (addNative_typed zeroNative_typed (Typing.var 0))
      (Typing.var 0))) formed₃
  have formed₁ : Typing R .nil identityTransportType U0 := pi_at numT_typed formed₂
  exact Typing.lamIntro (toIdentity formed₁) (isUniverseAt Tower.zero)
    (Typing.lamIntro (toIdentity formed₂) (isUniverseAt Tower.zero)
      (Typing.lamIntro (toIdentity formed₃) (isUniverseAt Tower.zero) body))

/-! ## Through the assumption and through its realization -/

/-- The declared assumption `subst@num` at its proof family, under the identity
reading. -/
theorem substConstant_typed :
    Typing identityRules .nil (.const SetProfile.substName) (Holds SetProfile.substCode) := by
  have typed := toIdentity (assumption_typed (Γ := .nil) 2)
  rw [SetProfile.liftClosed_zero] at typed
  exact typed

/-- The transport through the declared assumption. -/
def hostedTransport : Tower.Tm 0 := transportThrough (.const SetProfile.substName)

/-- The transport through the realization of substitution by identity
elimination. -/
def linkedTransport : Tower.Tm 0 := transportThrough substRealization

theorem hostedTransport_typed :
    Typing identityRules .nil hostedTransport identityTransportType :=
  transportThrough_typed substConstant_typed

theorem linkedTransport_typed :
    Typing identityRules .nil linkedTransport identityTransportType :=
  transportThrough_typed substRealization_typed

/-- Linking the hosted transport replaces the assumption by its realization. -/
theorem hostedTransport_linked :
    ConstantExpansion.expand linking hostedTransport = linkedTransport :=
  rfl

/-! ## Identity evidence at an open index -/

/-- A transport at the open index `k`, applied to evidence for `zero-add` at `k`
and to `refl (add zero k)`. -/
def identityAt (transport hosted : Tower.Tm 0) : Tower.Tm 1 :=
  .app (app2 (liftClosed transport) (.var 0) (.app (liftClosed hosted) (.var 0)))
    (.refl (addNative zeroNative (.var 0)))

/-- The runtime's construction: the declared transport at the retained source
proof. -/
def hostedIdentity : Tower.Tm 1 := identityAt hostedTransport SetProfile.zeroAddTerm

/-- The linked construction: the realized transport at the linked source proof. -/
def linkedIdentity : Tower.Tm 1 := identityAt linkedTransport linkedZeroAdd

/-- Linking the hosted construction gives the linked construction. -/
theorem hostedIdentity_linked :
    ConstantExpansion.expand linking hostedIdentity = linkedIdentity := by
  simp only [hostedIdentity, linkedIdentity, identityAt, app2, ConstantExpansion.expand,
    ConstantExpansion.expand_liftClosed, hostedTransport_linked]
  rfl

/-- Any transport of this type, at any proof of `zero-add`, is identity evidence
at the open index. -/
theorem identityAt_typed {transport hosted : Tower.Tm 0}
    (transportTyped : Typing identityRules .nil transport identityTransportType)
    (hostedTyped : Typing identityRules .nil hosted (Holds SetProfile.zeroAddCode)) :
    Typing identityRules indexContext (identityAt transport hosted)
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) := by
  have transportHere := FormationSensitiveHOLInterface.closed_typed transportTyped indexContext
  have decoded : Typing identityRules .nil hosted zeroAddDecoded :=
    Typing.conv hostedTyped (toIdentity (pi_at numT_typed
      (id_at numT_typed (addNative_typed zeroNative_typed (Typing.var 0)) (Typing.var 0))))
      (isUniverseAt Tower.zero)
      (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity identity_decodes
        SetProfile.zeroAddStatement SetProfile.zeroAdd_represented zeroAddStatement_decoded))
  have hostedHere := FormationSensitiveHOLInterface.closed_typed decoded indexContext
  have index : Typing R indexContext (.var 0) numT := Typing.var 0
  have point : Typing R indexContext (addNative zeroNative (.var 0)) numT :=
    addNative_typed zeroNative_typed index
  have atIndex : Typing identityRules indexContext (.app (liftClosed hosted) (.var 0))
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) :=
    Typing.appElim hostedHere (toIdentity index)
  have asHosted : Typing identityRules indexContext (.app (liftClosed hosted) (.var 0))
      (Holds (eqNumNative (addNative zeroNative (.var 0)) (.var 0))) :=
    Typing.conv atIndex (toIdentity (proof_typed (eqNum_typed point index)))
      (isUniverseAt Tower.zero) (.symm _ _ (holdsEq_identity _ _))
  exact Typing.appElim (Typing.appElim (Typing.appElim transportHere (toIdentity index)) asHosted)
    (Typing.reflIntro (toIdentity point))

/-- The retained source proof of `zero-add`, with its assumptions declared, under
the identity reading. -/
theorem zeroAddTerm_typed :
    Typing identityRules .nil SetProfile.zeroAddTerm (Holds SetProfile.zeroAddCode) :=
  toIdentity (include_target SetProfile.zeroAdd_typed)

theorem hostedIdentity_typed :
    Typing identityRules indexContext hostedIdentity
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) :=
  identityAt_typed hostedTransport_typed zeroAddTerm_typed

/-- The linked construction is identity evidence at the open index, with no
assumption left. -/
theorem linkedIdentity_typed :
    Typing identityRules indexContext linkedIdentity
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) :=
  identityAt_typed linkedTransport_typed linkedZeroAdd_typed

/-- The linked construction feeds the program's successor step at the open
index: `sucStep k (…) : Σ y : num. eqAt y`. -/
theorem linkedIdentity_feeds_sucStep :
    Typing identityRules indexContext (app2 (.const sucStepName) (.var 0) linkedIdentity)
      (.sigma numT (eqAtApp (.var 0))) := by
  have atEqAt : Typing identityRules indexContext linkedIdentity (eqAtApp (.var 0)) :=
    Typing.conv linkedIdentity_typed (toIdentity (eqAt_typed (Typing.var 0)))
      (isUniverseAt Tower.zero)
      (.symm _ _ (toIdentity_conversion (package_step listed_eqAt (at1 (.var 0)))))
  exact Typing.appElim
    (Typing.appElim (toIdentity (sucStep_typed _))
      (toIdentity (Typing.var (R := R) (Γ := indexContext) 0)))
    atEqAt

/-! ## Closed instances -/

/-- The linked construction at a numeral. -/
def closedIdentity (count : Nat) : Tower.Tm 0 :=
  .app (app2 linkedTransport (numeral count) (.app linkedZeroAdd (numeral count)))
    (.refl (addNative zeroNative (numeral count)))

theorem closedIdentity_instance (count : Nat) :
    inst0 (numeral count) linkedIdentity = closedIdentity count :=
  rfl

/-- The transport at an open index and open evidence, unfolded to identity
elimination: `id:eliminate num (add zero k) (λ y p. Holds (P y)) (refl (add zero k)) k e`,
with `P` the predicate `λ z. add zero k = z`. -/
def transportElimination : Tower.Tm 2 :=
  jApp numT (addNative zeroNative (.var 1))
    (.lam (.lam (Holds (.app (.lam (eqNumNative (addNative zeroNative (.var 4)) (.var 0)))
      (.var 1)))))
    (.refl (addNative zeroNative (.var 1))) (.var 1) (.var 0)

theorem transport_unfolds :
    Runs (.app (app2 (liftClosed linkedTransport) (.var 1) (.var 0))
        (.refl (addNative zeroNative (.var 1))) : Tower.Tm 2)
      transportElimination := by
  refine (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl).trans ?_
  refine (Runs.app (Runs.beta _ _) .refl).trans ?_
  refine (Runs.beta _ _).trans ?_
  refine (Runs.app (Runs.app (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl) .refl) .refl).trans ?_
  refine (Runs.app (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl) .refl).trans ?_
  refine (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl).trans ?_
  refine (Runs.app (Runs.beta _ _) .refl).trans ?_
  exact Runs.beta _ _

/-- At every numeral `m`, the linked construction runs to `refl m`: the source
proof at `m` runs to `refl m`, the point `add zero m` to `m`, and identity
elimination returns `refl (add zero m)`. -/
theorem closedIdentity_runs (count : Nat) :
    Runs (closedIdentity count) (.refl (numeral count)) := by
  have unfold := runs_substitute
    (patternValues ![numeral count, .app linkedZeroAdd (numeral count)]) transport_unfolds
  refine unfold.trans ?_
  refine (Runs.app (Runs.app (Runs.app (Runs.app (Runs.app .refl (add_zero_numeral count))
    .refl) .refl) .refl) (linkedZeroAdd_runs count)).trans ?_
  refine (Runs.equation listed_jIota (patternValues ![numT, numeral count, _, _])).trans ?_
  exact Runs.reflexivity (add_zero_numeral count)

theorem closedIdentity_typed (count : Nat) :
    Typing identityRules .nil (closedIdentity count)
      (.id numT (addNative zeroNative (numeral count)) (numeral count)) :=
  Typing.instantiate linkedIdentity_typed (toIdentity (numeral_typed count))

/-- Every run of the linked construction at `m` that stops, stops at `refl m`. -/
theorem closedIdentity_result (count : Nat) {result : Tower.Tm 0}
    (runs : StepStar identityRules (closedIdentity count) result)
    (stopped : Normal identityRules result) : result = .refl (numeral count) :=
  Metatheory.stopped_unique ⟨.nil, closedIdentity_typed count⟩ runs stopped
    (runs_toIdentity (closedIdentity_runs count))
    (Metatheory.identityDraft.normal_of_host (refl_numeral_normal count))

/-- The successor step consumes the closed construction:
`sucStep m (…)` runs to `(suc m, refl (suc m))`. -/
theorem closedIdentity_feeds_sucStep (count : Nat) :
    Runs (app2 (.const sucStepName) (numeral count) (closedIdentity count))
      (.pair (numeral (count + 1)) (.refl (numeral (count + 1)))) :=
  (Runs.app .refl (closedIdentity_runs count)).trans (sucStep_numeral count)

/-! ## Controls -/

theorem numeral_ne_succ {n : Nat} :
    ∀ count : Nat, (numeral count : Tower.Tm n) ≠ numeral (count + 1)
  | 0 => fun equal => by cases equal
  | count + 1 => fun equal => numeral_ne_succ count (Tm.app.inj equal).2

/-- The linked construction at `m` is not evidence that `add zero m` is `m + 1`. -/
theorem closedIdentity_wrong_index (count : Nat) :
    ¬ Typing Metatheory.identityLinearRules .nil (closedIdentity count)
      (.id numT (addNative zeroNative (numeral count)) (numeral (count + 1))) := by
  intro typed
  have reduct := (Metatheory.steps_preserve ⟨.nil, typed⟩
    (Metatheory.runs_linear (runs_toIdentity (closedIdentity_runs count)))).typing
  obtain ⟨_, toEndpoint⟩ := Metatheory.identityHost.refl_endpoints reduct
  exact numeral_ne_succ count (Metatheory.identityConstructors.eq_of_normal
    (Controls.numeral_normal count) (Controls.numeral_normal (count + 1)) toEndpoint)

/-- Reflexivity cannot take the place of the source proof: at the open index,
no reflexivity proof has the type of the transport's second argument. -/
theorem refl_not_hosted_open (witness : Tower.Tm 1) :
    ¬ Typing Metatheory.identityLinearRules indexContext (.refl witness)
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) := by
  intro typed
  obtain ⟨toPoint, toEndpoint⟩ := Metatheory.identityHost.refl_endpoints typed
  have same := Metatheory.identityConstructors.eq_of_normal (Controls.addZeroVar_normal 0)
    (Metatheory.identityConstructors.normal_var 0) (.trans _ _ _ (.symm _ _ toPoint) toEndpoint)
  cases same

/-- A term that no equation of the linearized program matches has no root step
there. -/
theorem linear_no_root {n : Nat} {term target : Tower.Tm n}
    (step : linearRules.computation.step term target)
    (natives : SetProfile.nativeEquations.all
      (fun equation => !instanceOf equation.2.1 term) = true)
    (package : linearEquations.all (fun equation => !instanceOf equation.2.1 term) = true)
    (implication : instanceOf implicationLeft term = false)
    (universal : ∀ type, instanceOf (universalLeft type) term = false) : False := by
  obtain ⟨m, left, right, rule, meets⟩ := linearConstructors.root_instance step
  cases rule with
  | implication => rw [implication] at meets; cases meets
  | universal type => rw [universal type] at meets; cases meets
  | native listed =>
      have excluded : (!instanceOf left term) = true := List.all_eq_true.mp natives _ listed
      rw [meets] at excluded
      cases excluded
  | package listed =>
      have excluded : (!instanceOf left term) = true := List.all_eq_true.mp package _ listed
      rw [meets] at excluded
      cases excluded

theorem linear_const_normal {n : Nat} (name : DeclName)
    (natives : SetProfile.nativeEquations.all
      (fun equation => !instanceOf equation.2.1 (.const name : Tower.Tm n)) = true)
    (package : linearEquations.all
      (fun equation => !instanceOf equation.2.1 (.const name : Tower.Tm n)) = true) :
    Normal linearRules (.const name : Tower.Tm n) :=
  Normal.const _ (fun step => linear_no_root step natives package rfl (fun _ => rfl))

theorem eqVar_normal : Normal linearRules (eqNumNative (.var 1) (.var 0) : Tower.Tm 2) :=
  Normal.app
    (Normal.app (linear_const_normal (SetProfile.eqName numTy) rfl rfl)
      (linearConstructors.normal_var 1) (fun _ equal => by cases equal)
      (fun step => linear_no_root step rfl rfl rfl (fun _ => rfl)))
    (linearConstructors.normal_var 0) (fun _ equal => by cases equal)
    (fun step => linear_no_root step rfl rfl rfl (fun _ => rfl))

/-- `Holds (x = y)` between two variables has no step outside the identity
reading. -/
theorem holdsEqVar_normal :
    Normal linearRules (Holds (eqNumNative (.var 1) (.var 0)) : Tower.Tm 2) :=
  Normal.app (linear_const_normal holdsName rfl rfl) eqVar_normal (fun _ equal => by cases equal)
    (fun step => linear_no_root step rfl rfl rfl (fun _ => rfl))

theorem idVar_normal :
    Normal linearRules (.id numT (.var 1) (.var 0) : Tower.Tm 2) := by
  intro target step
  cases step with
  | root rootStep => exact linearConstructors.no_root_of_spineHead rootStep rfl
  | congIdTy inner => exact linear_const_normal _ rfl rfl inner
  | congIdLeft inner => exact linearConstructors.normal_var 1 inner
  | congIdRight inner => exact linearConstructors.normal_var 0 inner

/-- Outside the identity reading, a represented equation between two variables
is not an identity type: the represented-family route keeps the source's
equality distinct from native identity. -/
theorem holdsEq_not_identity :
    ¬ Conv linearRules.headEq (Holds (eqNumNative (.var 1) (.var 0)) : Tower.Tm 2)
      (.id numT (.var 1) (.var 0)) linearRules.computation := by
  intro conversion
  have same := linearConstructors.eq_of_normal holdsEqVar_normal idVar_normal conversion
  cases same

/-- The same holds in the draft's program. -/
theorem holdsEq_not_identity_draft :
    ¬ Conv R.headEq (Holds (eqNumNative (.var 1) (.var 0)) : Tower.Tm 2)
      (.id numT (.var 1) (.var 0)) R.computation := by
  intro conversion
  apply holdsEq_not_identity
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head) Confluence.packageToLinear.headEq
      Confluence.packageToLinear.computation

#print axioms holdsEq_identity
#print axioms transportThrough_typed
#print axioms hostedTransport_typed
#print axioms linkedTransport_typed
#print axioms hostedTransport_linked
#print axioms hostedIdentity_linked
#print axioms hostedIdentity_typed
#print axioms linkedIdentity_typed
#print axioms linkedIdentity_feeds_sucStep
#print axioms closedIdentity_instance
#print axioms closedIdentity_runs
#print axioms closedIdentity_typed
#print axioms closedIdentity_result
#print axioms closedIdentity_feeds_sucStep
#print axioms closedIdentity_wrong_index
#print axioms refl_not_hosted_open
#print axioms holdsEq_not_identity
#print axioms holdsEq_not_identity_draft

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.HostedTransport
