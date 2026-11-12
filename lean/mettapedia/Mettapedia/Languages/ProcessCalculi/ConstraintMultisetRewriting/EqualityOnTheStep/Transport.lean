import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Run

/-!
# Transport along extensional equality, for every family with a respect term

The universal frame of transport (`Omega`) declares, in order:

  `P : (U0 → U0) → U1`, `r : Π (S T : U0 → U0). setEq S T → P S → P T`, `S T : U0 → U0`,
  `E : setEq S T`, `M : P S`.

A substitution `σ : Γ ⟶ Omega` is exactly a family with a respect term, two sets, evidence that they
are equal and a member of the family at the first, all typed over `Γ`. Over `Omega` the transported
member `r S T E M` has type `P T` (`transported_typed`); its instance along `σ` has type `σ(P) σ(T)` by
substitution.

**Transport is sound for every family that respects the equality** (`transportBy_admitted`,
`transportBy_made`): in any state with solvable knowledge, the firing that reads the evidence row and
the member row and makes `r S T E M` is admitted, and the made member is built from the codes of the
two rows it read. A family without a respect term has no instance of `Omega`: transport is not
defined for it. `Controls` shows a predicate on codes, and a family of the calculus, that have none.

**Membership respects the equality** (`memberFamily`, `memberRespect_typed`): `λS. S X` with the
respect term `λS T e m. fst (e X) m`. The classifying substitution `memberClassifier` gives the
family, its respect term, the sets `S` and `T`, the evidence `λX. (swap X, swapBack X)` and the member
`(x, g)`; the general transport at it is admitted and makes `memberRespect S T E (x, g)` at
`(λS. S X) T`, which is `T X` in the knowledge (`member_transport`, `member_family_at_T`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Transport

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## The universal frame -/

/-- `P : (U0 → U0) → U1`. -/
def pTy : TypeOver (empty Tower.rules) := ⟨famType, famLevel, .sort _, famType_formed _⟩

abbrev withP : Context Tower.rules := extend (empty Tower.rules) pTy

/-- `r : Π (S T : U0 → U0). setEq S T → P S → P T`. -/
def rTy : TypeOver withP := ⟨respType (.var 0), large, .sort _, respType_formed (Derivable.var 0)⟩

abbrev withR : Context Tower.rules := extend withP rTy

/-- `S : U0 → U0`. -/
def sTy : TypeOver withR := ⟨setType, large, .sort _, setType_large _⟩

abbrev withS : Context Tower.rules := extend withR sTy

/-- `T : U0 → U0`. -/
def tTy : TypeOver withS := ⟨setType, large, .sort _, setType_large _⟩

abbrev withT : Context Tower.rules := extend withS tTy

/-- `E : setEq S T`. -/
def eTy : TypeOver withT :=
  ⟨setEq (.var 1) (.var 0), large, .sort _, setEq_formed (Derivable.var 1) (Derivable.var 0)⟩

abbrev withE : Context Tower.rules := extend withT eTy

/-- `M : P S`. -/
def mTy : TypeOver withE := ⟨.app (.var 4) (.var 2), large, .sort _, famApp_typed (Derivable.var 4) (Derivable.var 2)⟩

/-- **The universal frame of transport.** -/
abbrev Omega : Context Tower.rules := extend withE mTy

/-- The evidence `E : setEq S T`, over the universal frame. -/
def evidenceRow : TotalTerm Omega :=
  ⟨⟨setEq (.var 3) (.var 2), large, .sort _, setEq_formed (Derivable.var 3) (Derivable.var 2)⟩,
    ⟨.var 1, Derivable.var 1⟩⟩

/-- The member `M : P S`, over the universal frame. -/
def memberRow : TotalTerm Omega :=
  ⟨⟨.app (.var 5) (.var 3), large, .sort _, famApp_typed (Derivable.var 5) (Derivable.var 3)⟩,
    ⟨.var 0, Derivable.var 0⟩⟩

/-- **The transported member is typed**: `r S T E M : P T`. -/
theorem transported_typed :
    Typed Tower.rules Omega.raw (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0))
      (.app (.var 5) (.var 2)) := by
  have r := Derivable.var (R := Tower.rules) (Γ := Omega.raw) 4
  have S := Derivable.var (R := Tower.rules) (Γ := Omega.raw) 3
  have T := Derivable.var (R := Tower.rules) (Γ := Omega.raw) 2
  have E := Derivable.var (R := Tower.rules) (Γ := Omega.raw) 1
  have M := Derivable.var (R := Tower.rules) (Γ := Omega.raw) 0
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim r S) T) E) M
  exact typed

/-- The transported member `r S T E M : P T`, over the universal frame. -/
def transportedRow : TotalTerm Omega :=
  ⟨⟨.app (.var 5) (.var 2), large, .sort _, famApp_typed (Derivable.var 5) (Derivable.var 2)⟩,
    ⟨.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0), transported_typed⟩⟩

/-! ## The transport firing, at any state -/

/-- **The transport firing** at a state, along a classifying substitution `σ`: it reads rows `i` (the
evidence) and `j` (the member) and makes row `k`, the transported member `σ(r S T E M)`. -/
def transportBy (st : State Tower.rules Nat) (i j k : Nat) (σ : st.frame ⟶ Omega) :
    Firing setting.levels st where
  helpers := .nil _
  taken := []
  read := [i, j]
  takes := []
  reads := [st.label i, st.label j]
  makes := [(k, Make.ofRow (transportedRow.reindex σ))]
  tells := []
  guards := []
  queries := []

/-- **Transport is admitted for every family with a respect term**: rows `i` and `j` present, row
`k` fresh, and the knowledge solvable. -/
theorem transportBy_admitted (st : State Tower.rules Nat) {i j k : Nat} (σ : st.frame ⟶ Omega)
    (hi : i ∈ st.present) (hj : j ∈ st.present) (hk : k ∉ st.present)
    (solvable : (frames setting.levels).Solvable st.knowledge) :
    (step setting.levels Nat).Admits (transportBy st i j k σ) := by
  obtain ⟨Θ, τ, solved⟩ := solvable
  have known : (frames setting.levels).applyStore (transportBy st i j k σ).helpers.weaken st.knowledge =
      st.knowledge := Frames.applyStore_id (X := frames setting.levels) st.knowledge
  have row_i : (transportBy st i j k σ).row i = st.label i := (frames setting.levels).act_id _
  have row_j : (transportBy st i j k σ).row j = st.label j := (frames setting.levels).act_id _
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff _).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨Θ, τ, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · rcases List.mem_cons.mp member with rfl | rest
    · exact hi
    · obtain rfl := List.mem_singleton.mp rest
      exact hj
  · obtain rfl := List.mem_singleton.mp member
    exact hk inside
  · intro e member
    rcases List.mem_append.mp member with front | told
    · rcases List.mem_append.mp front with front | readEq
      · rcases List.mem_append.mp front with knownEq | takenEq
        · rw [known] at knownEq
          exact solved e knownEq
        · exact absurd takenEq List.not_mem_nil
      · obtain ⟨x, inside, rfl⟩ := List.mem_map.mp readEq
        rcases List.mem_cons.mp inside with rfl | rest
        · show (frames setting.levels).E ((frames setting.levels).act τ (st.label i))
            ((frames setting.levels).act τ ((transportBy st i j k σ).row i))
          rw [row_i]
          exact ((frames setting.levels).equivalence _).refl _
        · obtain rfl := List.mem_singleton.mp rest
          show (frames setting.levels).E ((frames setting.levels).act τ (st.label j))
            ((frames setting.levels).act τ ((transportBy st i j k σ).row j))
          rw [row_j]
          exact ((frames setting.levels).equivalence _).refl _
    · exact absurd told List.not_mem_nil
  · intro b τ' _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The made member is built from the rows read**: when rows `i` and `j` are the evidence and the
member classified by `σ`, the made row is `r S T E M` with `E` and `M` the codes of those rows, at the
type `P T`. -/
theorem transportBy_made (st : State Tower.rules Nat) (i j : Nat) (σ : st.frame ⟶ Omega)
    (evidenceAt : st.label i = evidenceRow.reindex σ) (memberAt : st.label j = memberRow.reindex σ) :
    (transportedRow.reindex σ).2.code =
        .app (.app (.app (.app (σ.substitution 4) (σ.substitution 3)) (σ.substitution 2))
          (st.label i).2.code) (st.label j).2.code ∧
      (transportedRow.reindex σ).1.code = .app (σ.substitution 5) (σ.substitution 2) ∧
      (st.label i).1.code = setEq (σ.substitution 3) (σ.substitution 2) ∧
      (st.label j).1.code = .app (σ.substitution 5) (σ.substitution 3) := by
  rw [evidenceAt, memberAt]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The state of a classifying substitution: the evidence (row `0`) and the member (row `1`). -/
def classified (Γ : Context Tower.rules) (σ : Γ ⟶ Omega) : State Tower.rules Nat :=
  ⟨Γ, [], {0, 1}, fun o => if o = 0 then evidenceRow.reindex σ else memberRow.reindex σ⟩

theorem classified_transport_admitted (Γ : Context Tower.rules) (σ : Γ ⟶ Omega) :
    (step setting.levels Nat).Admits (transportBy (classified Γ σ) 0 1 2 σ) :=
  transportBy_admitted (classified Γ σ) σ (by show (0 : Nat) ∈ ({0, 1} : Finset Nat); decide)
    (by show (1 : Nat) ∈ ({0, 1} : Finset Nat); decide) (by show (2 : Nat) ∉ ({0, 1} : Finset Nat); decide)
    ⟨Γ, 𝟙 Γ, Frames.models_nil _⟩

/-! ## Membership is a family with a respect term -/

/-- **Membership at `A`**: the family `λS. S A`. -/
def memberFamily {n : Nat} (A : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (.var 0) (Presentation.rename wk A))

theorem memberFamily_typed {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} (tA : Typed Tower.rules Γ A U0) :
    Typed Tower.rules Γ (memberFamily A) famType :=
  .lamIntro (famType_formed Γ) (.sort _) (.cumul (Run.app_small (Derivable.var 0) tA.weaken) small_large)

/-- **The respect term of membership** at the variable `X` of `X : U0, x : X, g : Ground`:
`λS T e m. fst (e X) m`. -/
def memberRespect : Tower.Tm 3 :=
  .lam (.lam (.lam (.lam (.app (.fst (.app (.var 1) (.var 6))) (.var 0)))))

/-- The frame of its body: `X : U0, x : X, g : Ground, S T : U0 → U0, e : setEq S T, m : S X`. -/
abbrev respectBody : Tower.Ctx 7 :=
  .snoc (.snoc (.snoc (.snoc triple.raw setType) setType) (setEq (.var 1) (.var 0)))
    (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
      (memberFamily (.var 2 : Tower.Tm 3))))) (.var 2))

theorem member_body_typed :
    Typed Tower.rules respectBody (.app (.fst (.app (.var 1) (.var 6))) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (memberFamily (.var 2 : Tower.Tm 3)))))) (.var 2)) := by
  have bodyFamily : Typed Tower.rules (.snoc respectBody setType) (.app (.var 0) (.var 7)) (.head large) :=
    .cumul (Run.app_small (Derivable.var 0) (Derivable.var 7)) small_large
  have e : Typed Tower.rules respectBody (.var 1) (setEq (.var 3) (.var 2)) := Derivable.var 1
  have X : Typed Tower.rules respectBody (.var 6) U0 := Derivable.var 6
  have forward : Typed Tower.rules respectBody (.fst (.app (.var 1) (.var 6)))
      (.pi (.app (.var 3) (.var 6)) (.app (.var 3) (.var 7))) := Derivable.fstElim (Derivable.appElim e X)
  have m : Typed Tower.rules respectBody (.var 0) (.app (.lam (.app (.var 0) (.var 7))) (.var 3)) :=
    Derivable.var 0
  have atS : Equal Tower.rules respectBody (.app (.lam (.app (.var 0) (.var 7))) (.var 3))
      (.app (.var 3) (.var 6)) (.head large) :=
    Derivable.betaPi (famType_formed _) (.sort _) bodyFamily (Derivable.var 3)
  have atT : Equal Tower.rules respectBody (.app (.lam (.app (.var 0) (.var 7))) (.var 2))
      (.app (.var 2) (.var 6)) (.head large) :=
    Derivable.betaPi (famType_formed _) (.sort _) bodyFamily (Derivable.var 2)
  have result : Typed Tower.rules respectBody (.app (.fst (.app (.var 1) (.var 6))) (.var 0))
      (.app (.var 2) (.var 6)) :=
    Derivable.appElim forward (.conv m atS (.sort _))
  exact .conv result (.symm atT) (.sort _)

/-- **Membership respects extensional equality**: `λS T e m. fst (e X) m` is a respect term for
`λS. S X`. -/
theorem memberRespect_typed :
    Typed Tower.rules triple.raw memberRespect (respType (memberFamily (.var 2 : Tower.Tm 3))) := by
  have tP : Typed Tower.rules triple.raw (memberFamily (.var 2 : Tower.Tm 3)) famType :=
    memberFamily_typed (Derivable.var 2)
  have l4 := Derivable.lamIntro (respInner_formed tP) (.sort _) member_body_typed
  have l3 := Derivable.lamIntro (respThird_formed tP) (.sort _) l4
  have l2 := Derivable.lamIntro (respSecond_formed tP) (.sort _) l3
  exact Derivable.lamIntro (respType_formed tP) (.sort _) l2

/-- The member `(x, g)`, at the family's type `(λS. S X) S`. -/
theorem member_at_family :
    Typed Tower.rules triple.raw (.pair (.var 1) (.var 0)) (.app (memberFamily (.var 2 : Tower.Tm 3)) sCode) := by
  have bodyFamily : Typed Tower.rules (.snoc triple.raw setType) (.app (.var 0) (.var 3)) (.head large) :=
    .cumul (Run.app_small (Derivable.var 0) (Derivable.var 3)) small_large
  have beta : Equal Tower.rules triple.raw (.app (memberFamily (.var 2 : Tower.Tm 3)) sCode)
      (.app sCode (.var 2)) (.head large) :=
    Derivable.betaPi (famType_formed _) (.sort _) bodyFamily (s_typed _)
  exact .conv Run.member_typed (.symm beta) (.sort _)

/-- `(λS. S X) T` is `T X`. -/
theorem member_family_at_T :
    Equal Tower.rules triple.raw (.app (memberFamily (.var 2 : Tower.Tm 3)) tCode) (.app tCode (.var 2))
      (.head large) := by
  have bodyFamily : Typed Tower.rules (.snoc triple.raw setType) (.app (.var 0) (.var 3)) (.head large) :=
    .cumul (Run.app_small (Derivable.var 0) (Derivable.var 3)) small_large
  exact Derivable.betaPi (famType_formed _) (.sort _) bodyFamily (t_typed _)

/-- **The classifying substitution of membership**: the family `λS. S X`, its respect term, the sets
`S` and `T`, the evidence `λX. (swap X, swapBack X)` and the member `(x, g)`. -/
def memberClassifier : triple ⟶ Omega :=
  pair (pair (pair (pair (pair (pair (toEmpty triple)
    ⟨memberFamily (.var 2 : Tower.Tm 3), memberFamily_typed (Derivable.var 2)⟩)
    ⟨memberRespect, memberRespect_typed⟩) ⟨sCode, s_typed _⟩) ⟨tCode, t_typed _⟩)
    ⟨Run.evidenceAt, Run.evidenceAt_typed⟩) ⟨.pair (.var 1) (.var 0), member_at_family⟩

/-- **Membership transports, as an instance of the general transport**: the firing is admitted, and
it makes `memberRespect S T E (x, g)` at `(λS. S X) T`, which is `T X` in the knowledge. -/
theorem member_transport :
    (step setting.levels Nat).Admits (transportBy (classified triple memberClassifier) 0 1 2 memberClassifier) ∧
      (transportedRow.reindex memberClassifier).2.code =
        .app (.app (.app (.app memberRespect sCode) tCode) Run.evidenceAt) (.pair (.var 1) (.var 0)) ∧
      (transportedRow.reindex memberClassifier).1.code = .app (memberFamily (.var 2 : Tower.Tm 3)) tCode :=
  ⟨classified_transport_admitted triple memberClassifier, rfl, rfl⟩

end EqualityOnTheStep.Transport

#print axioms EqualityOnTheStep.Transport.transported_typed
#print axioms EqualityOnTheStep.Transport.transportBy_admitted
#print axioms EqualityOnTheStep.Transport.transportBy_made
#print axioms EqualityOnTheStep.Transport.classified_transport_admitted
#print axioms EqualityOnTheStep.Transport.memberRespect_typed
#print axioms EqualityOnTheStep.Transport.member_family_at_T
#print axioms EqualityOnTheStep.Transport.member_transport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
