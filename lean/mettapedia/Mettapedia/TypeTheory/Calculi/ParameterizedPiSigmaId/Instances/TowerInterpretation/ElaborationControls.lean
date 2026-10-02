import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Examples

/-!
# Controls: elaboration of the tower, carried into the set tower

* **Positive: the domains of a Curry-style term are reconstructed, and its value is the one
  computed for its annotated form.** The candidate polymorphic identity `λ X. λ x. x`, at
  `Π (X : U₀). X → X`, has no domains. Every elaboration of it is
  `λ (X : D₁). λ (x : D₂). x` with `D₁ ≡ U₀` and `D₂ ≡ X` (`polyId_lift_domains`,
  `polyId_lifts`), and its value in the tower model is the trace of the family of identity
  graphs over the small sets, whatever the elaboration (`polyId_lift_value`).
* **Positive: an abstraction in function position.** `(λ (X : U₀). X) G` and
  `(λ (X : U₁). X) G`, at the ground head `G`, have one erasure and are both typed at `U₁`
  (`redex0_typed`, `redex1_typed`), although `U₀` and `U₁` are not equal types
  (`universes_not_equal`): here the domain is not determined even up to equality. Coherence
  equates the two (`redexes_equal`), and both denote the ground set (`redexes_value`).
* **Negative: a judgment over an ill-formed context does not elaborate.** Over `x : λ y. y`,
  whose entry is no type, `x : λ y. y` and the type `U₀` are candidate judgments
  (`illFormed_var_typed`, `illFormed_isType`), but no formed annotated context erases to that
  context (`illFormed_no_lift`), since no abstraction is a type (`lam_not_type`). Through the
  elaboration of formed contexts, the context is not formed (`illFormed_not_formed`).
* **Negative: injectivity of the type formers separates the elaborations of one term.** The
  identities on `U₀` and on `U₁` have one erasure and are equal at no type
  (`idU_not_equal`), now that the annotated type formers are injective (`towerFormerFacts`).
* **Positive: λ-congruence across distinct but equal domains.** `λ (x : U₀). x` and
  `λ (x : U_{max 0 0}). x` have distinct domains (`U0_ne_Um`) that are equal types (`U0_Um`).
  The annotated judgment equates them by one rule `lamCong` (`lamCong_equal_domains`, the
  equation of `TowerControls.headEq_coherent`). η and β derive the same equation without that
  rule (`lamCong_by_eta`); functionality derives it by substituting `U₀ ≡ U_{max 0 0}` for `X`
  in `λ (x : X). x` (`lamCong_by_functionality`). The rule holds in every set model
  (`Holds.lamCong`).
* **Negative: an abstraction over an ill-formed domain is rejected.** The abstraction
  `λ (X : U₀). X` is a type at no universe, so the domain premise of `lamIntro` fails for it
  (`badDomain_not_type`), and no abstraction over it has any type (`lam_badDomain_untyped`).
* Consistency: the type `Π (X : U₀). X` has no closed candidate inhabitant
  (`candidate_consistent`), while `Π (X : U₀). X → X` has one (`polyId_raw`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace ElaborationControls

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open TowerControls (U l0 l1 idU)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp)

universe u

/-! ## Positive: the domains of a Curry-style term are reconstructed -/

/-- The candidate polymorphic identity `λ X. λ x. x` at `Π (X : U₀). X → X`: no domains. -/
theorem polyId_raw :
    Typed Tower.rules .nil (.lam (.lam (.var 0))) (Examples.polyIdType.erase) :=
  Examples.polyId_candidate

/-- **Every elaboration of the polymorphic identity reconstructs both domains**: it is
`λ (X : D₁). λ (x : D₂). x` at the annotated `Π (X : U₀). X → X`, with `D₁ ≡ U₀` and
`D₂ ≡ X`. -/
theorem polyId_lift_domains {t' A' : CTm Tower.Head 0} (et : t'.erase = .lam (.lam (.var 0)))
    (eA : A'.erase = Examples.polyIdType.erase) (typing : CTyped TowerControls.P₀ .nil t' A') :
    ∃ D₁ D₂, t' = .lam D₁ (.lam D₂ (.var 0)) ∧ A' = Examples.polyIdType ∧
      CTypeEq TowerControls.P₀ .nil D₁ (U l0) ∧
      CTypeEq TowerControls.P₀ (.snoc .nil (U l0)) D₂ (.var 0) := by
  obtain ⟨D₁, b, rfl, eb⟩ := CTm.erase_eq_lam et
  obtain ⟨D₂, c, rfl, ec⟩ := CTm.erase_eq_lam eb
  obtain rfl := CTm.erase_eq_var ec
  obtain rfl : A' = Examples.polyIdType := CTm.eq_of_erase_eq_of_lamFree eA rfl
  obtain ⟨eD₁, tb⟩ := CTyped.lam_inv towerFormerFacts towerLevels typing .nil
  have formed : CCtxFormed TowerControls.P₀ (.snoc .nil (U l0)) :=
    .snoc .nil ⟨_, .sort _, TowerControls.univ_typed l0⟩
  exact ⟨D₁, D₂, rfl, rfl, eD₁, (CTyped.lam_inv towerFormerFacts towerLevels tb formed).1⟩

/-- **The polymorphic identity elaborates.** -/
theorem polyId_lifts : ∃ D₁ D₂,
    CTyped TowerControls.P₀ .nil (.lam D₁ (.lam D₂ (.var 0))) Examples.polyIdType ∧
      CTypeEq TowerControls.P₀ .nil D₁ (U l0) := by
  obtain ⟨t', A', et, eA, typing⟩ := tower_lifts polyId_raw CCtxFormed.nil rfl
  obtain ⟨D₁, D₂, rfl, rfl, eD₁, -⟩ := polyId_lift_domains et eA typing
  exact ⟨D₁, D₂, typing, eD₁⟩

/-- **The value of every elaboration of the polymorphic identity** in the tower model is the
trace of the family of identity graphs over the small sets: the value computed for the
annotated polymorphic identity (`Examples.ev_polyId`). -/
theorem polyId_lift_value (h : CofinalInaccessibles.{u}) {t' A' : CTm Tower.Head 0}
    (et : t'.erase = .lam (.lam (.var 0))) (eA : A'.erase = Examples.polyIdType.erase)
    (typing : CTyped TowerControls.P₀ .nil t' A') :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) t' Fin.elim0 =
      traceLam (graph (universeSet h ∅ 0) (fun X => traceLam (graph X (fun x => x)))) := by
  obtain rfl : A' = Examples.polyIdType := CTm.eq_of_erase_eq_of_lamFree eA rfl
  have equal := tower_coherence .nil typing Examples.polyId_typed (by rw [et]; rfl)
  have value := CDerivable.sound_equality (standardTowerModel h) equal Fin.elim0
    (sat_nil _ _ Fin.elim0)
  exact value.trans (Examples.ev_polyId h)

/-! ## Positive: an abstraction in function position -/

/-- The ground head. -/
abbrev G {n : Nat} : CTm Tower.Head n := .head .legacyGround

/-- `(λ (X : D). X) G`. -/
abbrev redexAt (D : CTm Tower.Head 0) : CTm Tower.Head 0 := .app (.lam D (.var 0)) G

theorem ground_typed {n : Nat} {Γ : CCtx Tower.Head n} : CTyped TowerControls.P₀ Γ G (U l0) :=
  .headType LevelTower.HeadTyping.legacyGround

/-- `(λ (X : U₀). X) G` is typed at `U₁`. -/
theorem redex0_typed : CTyped TowerControls.P₀ .nil (redexAt (U l0)) (U l1) :=
  CDerivable.cumul (.appElim (TowerControls.idU_typed l0) ground_typed) TowerControls.cumul01

/-- `(λ (X : U₁). X) G` is typed at `U₁`. -/
theorem redex1_typed : CTyped TowerControls.P₀ .nil (redexAt (U l1)) (U l1) :=
  .appElim (TowerControls.idU_typed l1) (CDerivable.cumul ground_typed TowerControls.cumul01)

/-- The two redexes have one erasure. -/
theorem redexes_erase : (redexAt (U l0)).erase = (redexAt (U l1)).erase := rfl

/-- **`U₀` and `U₁` are not equal types**: their levels differ. -/
theorem universes_not_equal :
    ¬ CTypeEq TowerControls.P₀ (.nil : CCtx Tower.Head 0) (U l0) (U l1) :=
  fun equal => by
    rcases CTypeEq.head_injective towerFormerFacts equal .nil with same | same
    · cases same
    · exact absurd (same fun _ => 0) (by decide)

/-- **Coherence equates the two redexes**, although their domains are not equal. -/
theorem redexes_equal : CEqual TowerControls.P₀ .nil (redexAt (U l0)) (redexAt (U l1)) (U l1) :=
  tower_coherence .nil redex0_typed redex1_typed redexes_erase

/-- **Both redexes denote the ground set** in the tower model. -/
theorem redexes_value (h : CofinalInaccessibles.{u}) :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) (redexAt (U l0)) Fin.elim0 = ∅ ∧
      ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) (redexAt (U l1)) Fin.elim0 = ∅ := by
  have value₀ : ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) (redexAt (U l0))
      Fin.elim0 = ∅ := Examples.ev_betaRedex h
  exact ⟨value₀, (CDerivable.sound_equality (standardTowerModel h) redexes_equal Fin.elim0
    (sat_nil _ _ Fin.elim0)).symm.trans value₀⟩

/-! ## Negative: a judgment over an ill-formed context does not elaborate -/

/-- The context `x : λ y. y`, whose entry is no type. -/
abbrev ctxBad : Tower.Ctx 1 := .snoc .nil (.lam (.var 0))

/-- The variable of the ill-formed context is typed at its entry. -/
theorem illFormed_var_typed : Typed Tower.rules ctxBad (.var 0) (.lam (.var 0)) := by
  have h := Derivable.var (R := Tower.rules) (Γ := ctxBad) 0
  exact h

/-- `U₀` is a type of the ill-formed context. -/
theorem illFormed_isType : Normalization.IsType Tower.rules ctxBad (.head (.sort Tower.zero)) :=
  ⟨_, .sort _, .headType (.sort Tower.zero)⟩

/-- **No abstraction is an annotated type.** -/
theorem lam_not_type {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed TowerControls.P₀ Γ)
    {D : CTm Tower.Head n} {b : CTm Tower.Head (n + 1)} :
    ¬ CIsType TowerControls.P₀ Γ (.lam D b) := by
  rintro ⟨u, hu, typing⟩
  obtain ⟨B, u', w, _, _, tPi, hu', _, le⟩ := typing.generation
  have below := CTypeLe.toBelow le (CIsType.head_of_universe towerLevels hu)
  obtain ⟨A', B', eT, -, -⟩ := CBelow.pi_source towerFormerFacts towerLevels below formed
    (CIsType.refl ⟨u', hu', tPi⟩)
  exact CTypeEq.pi_ne_head towerFormerFacts formed eT.symm

/-- **No formed annotated context erases to the ill-formed context.** -/
theorem illFormed_no_lift :
    ¬ ∃ Γ' : CCtx Tower.Head 1, CCtxFormed TowerControls.P₀ Γ' ∧ Γ'.erase = ctxBad := by
  rintro ⟨Γ', formed, e⟩
  cases formed with
  | snoc formed₀ type =>
      obtain ⟨-, eA⟩ := Ctx.snoc.inj e
      obtain ⟨D, b, rfl, -⟩ := CTm.erase_eq_lam eA
      exact lam_not_type formed₀ type

/-- **The type `U₀` over the ill-formed context does not elaborate**, although it is a type
there: the elaboration of types fails without its hypothesis on the context. -/
theorem illFormed_type_not_lifted :
    ¬ ∃ (Γ' : CCtx Tower.Head 1) (A' : CTm Tower.Head 1), CCtxFormed TowerControls.P₀ Γ' ∧
      Γ'.erase = ctxBad ∧ A'.erase = .head (.sort Tower.zero) ∧
        CIsType TowerControls.P₀ Γ' A' :=
  fun ⟨Γ', _, formed, e, _⟩ => illFormed_no_lift ⟨Γ', formed, e⟩

/-- **The ill-formed context is not formed**, through the elaboration of formed contexts. -/
theorem illFormed_not_formed : ¬ Normalization.CtxFormed Tower.rules ctxBad :=
  fun formed => illFormed_no_lift (tower_lift_ctxFormed formed)

/-! ## Negative: injectivity separates the elaborations of one term -/

/-- **The identities on `U₀` and on `U₁`**, one erasure, are equal at no type of a formed
context. -/
theorem idU_not_equal {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed TowerControls.P₀ Γ)
    (T : CTm Tower.Head n) : ¬ CEqual TowerControls.P₀ Γ (idU l0) (idU l1) T :=
  TowerControls.idU_not_equal towerFormerFacts formed T

/-! ## λ-congruence across distinct but equal domains -/

/-- `U_{max 0 0}`. -/
abbrev Um {n : Nat} : CTm Tower.Head n := .head (.sort (.max Tower.zero Tower.zero))

/-- `U₀` and `U_{max 0 0}` are distinct terms. -/
theorem U0_ne_Um {n : Nat} : (U0 : CTm Tower.Head n) ≠ Um := by
  intro same
  cases same

/-- `U₀ ≡ U_{max 0 0} : U₁`, by head equality, in the annotated judgment. -/
theorem U0_Um {n : Nat} {Γ : CCtx Tower.Head n} :
    CDerivable towerPackage (.equality Γ U0 Um (.head (.sort (.succ Tower.zero)))) := by
  have raise : Tower.rules.cumulative (.sort (.succ (.max Tower.zero Tower.zero)))
      (.sort (.succ Tower.zero)) := fun _ => le_refl _
  exact .headEq (show Tower.HeadEq (.sort Tower.zero) (.sort (.max Tower.zero Tower.zero)) from
      fun _ => rfl) (.headType (LevelTower.HeadTyping.sort Tower.zero))
    (.sub (.headType (LevelTower.HeadTyping.sort _)) (.subUniv raise))

/-- `Π (x : D). D` is a type, for `D` the universe at `0` or at `max 0 0`. -/
theorem piUniv_typed {n : Nat} {Γ : CCtx Tower.Head n} (l : LevelExpr Nat) :
    CDerivable towerPackage (.typing Γ (.pi (.head (.sort l)) (.head (.sort l)))
      (.head (.sort (.max (.succ l) (.succ l))))) :=
  .piForm (.headType (LevelTower.HeadTyping.sort l)) (.sort _) (.headType (LevelTower.HeadTyping.sort l))
    (.sort _) (.sorts _ _)

/-- **λ-congruence across distinct but equal domains**: the annotated judgment relates
`λ (x : U₀). x` and `λ (x : U_{max 0 0}). x` by one rule `lamCong`, from `U₀ ≡ U_{max 0 0}`. This
is the equation of `TowerControls.headEq_coherent`. -/
theorem lamCong_equal_domains :
    CDerivable towerPackage (.equality .nil (.lam U0 (.var 0)) (.lam Um (.var 0)) (.pi U0 U0)) :=
  .lamCong U0_Um (.sort _) (piUniv_typed _) (.sort _) (.refl (.var 0))

/-- **The same equation by η and β**, without the rule `lamCong`: in this instance the rule
derives nothing that η and β do not. -/
theorem lamCong_by_eta :
    CDerivable towerPackage (.equality .nil (.lam U0 (.var 0)) (.lam Um (.var 0)) (.pi U0 U0)) := by
  have tf : CDerivable towerPackage (.typing .nil (.lam U0 (.var 0)) (.pi U0 U0)) :=
    Examples.idU0_typed
  have tg₀ : CDerivable towerPackage (.typing .nil (.lam Um (.var 0)) (.pi Um Um)) :=
    .lamIntro (.headType (LevelTower.HeadTyping.sort _)) (.sort _) (piUniv_typed _) (.sort _) (.var 0)
  have ePi : CDerivable towerPackage (.equality .nil (.pi Um Um) (.pi U0 U0)
      (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero))))) :=
    .piCong (.symm U0_Um) (.sort _) (.symm U0_Um) (.sort _) (.sorts _ _)
  have tg : CDerivable towerPackage (.typing .nil (.lam Um (.var 0)) (.pi U0 U0)) :=
    .conv tg₀ ePi (.sort _)
  have x0 : CDerivable (towerPackage (L := Nat)) (.typing (.snoc .nil U0) (.var 0) U0) := .var 0
  have left : CDerivable towerPackage (.equality (.snoc .nil U0)
      (.app (.lam U0 (.var 0)) (.var 0)) (.var 0) U0) :=
    .betaPi (A := U0) (B := U0) (body := .var 0) (a := .var 0) (piUniv_typed _) (.sort _) (.var 0)
      x0
  have xm : CDerivable towerPackage (.typing (.snoc .nil U0) (.var 0) Um) :=
    .conv x0 U0_Um (.sort _)
  have right : CDerivable towerPackage (.equality (.snoc .nil U0)
      (.app (.lam Um (.var 0)) (.var 0)) (.var 0) Um) :=
    .betaPi (A := Um) (B := Um) (body := .var 0) (a := .var 0) (piUniv_typed _) (.sort _) (.var 0)
      xm
  have right' : CDerivable towerPackage (.equality (.snoc .nil U0)
      (.app (.lam Um (.var 0)) (.var 0)) (.var 0) U0) :=
    .convEq right (.symm U0_Um) (.sort _)
  exact .etaPi tf tg (.trans left (.symm right'))

/-- **The same equation by functionality**: substituting the equal types `U₀ ≡ U_{max 0 0}` for
`X` in `λ (x : X). x` substitutes them into its domain (`CDerivable.functional`). -/
theorem lamCong_by_functionality :
    CDerivable towerPackage (.equality .nil (.lam U0 (.var 0)) (.lam Um (.var 0)) (.pi U0 U0)) := by
  have typing : CDerivable towerPackage (.typing (.snoc .nil (.head (.sort (.succ Tower.zero))))
      (.lam (.var 0) (.var 0)) (.pi (.var 0) (.var 1))) :=
    .lamIntro (.var 0) (.sort _) (.piForm (.var 0) (.sort _) (.var 1) (.sort _) (.sorts _ _))
      (.sort _) (.var 0)
  have substEq : CSubstEq towerPackage (.snoc .nil (.head (.sort (.succ Tower.zero)))) .nil
      (fun _ => U0) (fun _ => Um) :=
    ⟨fun i => Fin.cases (.headType (LevelTower.HeadTyping.sort Tower.zero)) (·.elim0) i,
      fun i => Fin.cases U0_Um (·.elim0) i⟩
  exact CDerivable.functional typing substEq

/-! ## Negative: an abstraction over an ill-formed domain is rejected -/

/-- `λ (X : U₀). X`, an abstraction, offered as a domain. -/
abbrev badDomain {n : Nat} : CTm Tower.Head n := .lam U0 (.var 0)

/-- **The domain premise of `lamIntro` fails for an abstraction**: `λ (X : U₀). X` is a type at
no universe. -/
theorem badDomain_not_type {w : Tower.Head} (hw : Tower.rules.isUniverse w) :
    ¬ CDerivable towerPackage (.typing .nil badDomain (.head w)) :=
  fun typing => lam_not_type .nil ⟨w, hw, typing⟩

/-- **No abstraction over an ill-formed domain has a type**: whatever its body and its type,
`λ (x : λ (X : U₀). X). b` has no derivation, since every typing of an abstraction types its
domain at a universe (`CTyped.generation`). -/
theorem lam_badDomain_untyped (body : CTm Tower.Head 1) (T : CTm Tower.Head 0) :
    ¬ CDerivable towerPackage (.typing .nil (.lam badDomain body) T) := by
  intro typing
  obtain ⟨_, _, w, tA, hw, -⟩ := CTyped.generation typing
  exact badDomain_not_type hw tA

end ElaborationControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
