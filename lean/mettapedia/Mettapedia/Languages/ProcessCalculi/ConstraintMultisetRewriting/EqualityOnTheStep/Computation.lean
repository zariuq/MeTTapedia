import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Run

/-!
# Transport computes

At the solution of `Run`, the transported member reads `fst ((λX. (swap X, swapBack X)) X) (x, g)`
(`Run.transported_row`). In the knowledge it is the swapped pair `(g, x) : T X`
(`coercion_computes`, `transported_member_computes`): the coercion along the extensionality evidence
β-reduces to the forward swap, and the swap to the swapped pair. The transported member is a
canonical form; no coercion is stuck.

**The evidence is an equivalence** (`swap_round_trip`, `round_trip_witness`): `swapBack X (swap X p)`
is `p` in the knowledge, by β and pair η, so `refl p` proves `Id (S X) (swapBack X (swap X p)) p`.
What a univalent design would record as a path `S = T` is here a row together with round trips that
the knowledge decides.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Computation

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-- The forward swap's body over `X : U0`: `λp. (snd p, fst p) : Σ X Ground → Σ Ground X`. -/
theorem swapInner_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.lam (.pair (.snd (.var 0)) (.fst (.var 0))))
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) := by
  have pairs : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
  have p : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.var 0) (.sigma (.var 1) ground) :=
    Derivable.var 0
  have body : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 2)) :=
    .pairIntro pairs (.sort _) (.sndElim p) (.fstElim p)
  have innerFormed : Typed Tower.rules (.snoc Γ U0) (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) U0 :=
    .cumul (.piForm (sBody_typed Γ) (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  exact .lamIntro innerFormed (.sort _) body

/-- **The coercion along the extensionality evidence computes**: over `X : U0, x : X, g : Ground`,
`fst ((λX. (swap X, swapBack X)) X) (x, g)` is `(g, x)` at `T X`. -/
theorem coercion_computes :
    Equal Tower.rules triple.raw (.app (.fst (.app Run.evidenceAt (.var 2))) (.pair (.var 1) (.var 0)))
      (.pair (.var 0) (.var 1)) (.app tCode (.var 2)) := by
  have tX : Typed Tower.rules triple.raw (.var 2) U0 := Derivable.var 2
  have x : Typed Tower.rules triple.raw (.var 1) (.var 2) := Derivable.var 1
  have g : Typed Tower.rules triple.raw (.var 0) ground := Derivable.var 0
  have memberFormed : Typed Tower.rules triple.raw (.sigma (.var 2) ground) U0 :=
    .cumul (.sigmaForm tX (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have m : Typed Tower.rules triple.raw (.pair (.var 1) (.var 0)) (.sigma (.var 2) ground) :=
    .pairIntro memberFormed (.sort _) x g
  -- the evidence at `X` is the pair of the two swaps at `X`
  have fX := Derivable.appElim (swap_typed (.snoc triple.raw U0))
    (Derivable.var (R := Tower.rules) (Γ := .snoc triple.raw U0) 0)
  have gX := Derivable.appElim (swapBack_typed (.snoc triple.raw U0))
    (Derivable.var (R := Tower.rules) (Γ := .snoc triple.raw U0) 0)
  have evBody := Derivable.pairIntro (stSigma_formed triple.raw) (.sort _) fX gX
  have b1 := Derivable.betaPi (stNormal_formed triple.raw) (.sort _) evBody tX
  have b2 := Derivable.fstCong b1
  have sigX := (stSigma_formed triple.raw).substitute (SubstMor.single tX)
  have forwardAtX := Derivable.appElim (swap_typed triple.raw) tX
  have backwardAtX := Derivable.appElim (swapBack_typed triple.raw) tX
  have b3 := Derivable.betaFst sigX (.sort _) forwardAtX backwardAtX
  have fstEq := Derivable.trans b2 b3
  -- apply it to the member
  have a1 := Derivable.appCong fstEq (Derivable.refl m)
  -- the forward swap at `X` is `λp. (snd p, fst p)`
  have c1 := Derivable.betaPi (swapType_formed triple.raw) (.sort _) (swapInner_typed triple.raw) tX
  have a2 := Derivable.appCong c1 (Derivable.refl m)
  -- `(λp. (snd p, fst p)) (x, g)` is `(snd (x, g), fst (x, g))`
  have pairs : Typed Tower.rules (.snoc triple.raw (.sigma (.var 2) ground)) (.sigma ground (.var 4)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 4) (.sort _) (.sorts _ _)) collapse
  have p : Typed Tower.rules (.snoc triple.raw (.sigma (.var 2) ground)) (.var 0) (.sigma (.var 3) ground) :=
    Derivable.var 0
  have swapped : Typed Tower.rules (.snoc triple.raw (.sigma (.var 2) ground))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 4)) :=
    .pairIntro pairs (.sort _) (.sndElim p) (.fstElim p)
  have forwardFormed : Typed Tower.rules triple.raw (.pi (.sigma (.var 2) ground) (.sigma ground (.var 4))) U0 :=
    .cumul (.piForm memberFormed (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  have a3 := Derivable.betaPi forwardFormed (.sort _) swapped m
  -- and that is `(g, x)`
  have sgFormed : Typed Tower.rules triple.raw (.sigma ground (.var 3)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 3) (.sort _) (.sorts _ _)) collapse
  have a4 := Derivable.pairCong sgFormed (.sort _) (Derivable.betaSnd memberFormed (.sort _) x g)
    (Derivable.betaFst memberFormed (.sort _) x g)
  have chain : Equal Tower.rules triple.raw (.app (.fst (.app Run.evidenceAt (.var 2))) (.pair (.var 1) (.var 0)))
      (.pair (.var 0) (.var 1)) (.sigma ground (.var 3)) :=
    .trans a1 (.trans a2 (.trans a3 a4))
  exact .convEq chain (.symm (t_beta tX)) (.sort _)

/-- **At the run's solution, the transported member is `(g, x) : T X`** in the knowledge. -/
theorem transported_member_computes :
    Equal Tower.rules triple.raw (subst Run.transSolution.substitution (Run.final.label 4).2.code)
      (.pair (.var 0) (.var 1)) (subst Run.transSolution.substitution (Run.final.label 4).1.code) := by
  rw [Run.transported_row.2.2, Run.transported_row.2.1]
  exact coercion_computes

/-! ## The two swaps are mutually inverse in the knowledge -/

/-- The backward swap's body over `X : U0`: `λq. (snd q, fst q) : Σ Ground X → Σ X Ground`. -/
theorem swapBackInner_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.lam (.pair (.snd (.var 0)) (.fst (.var 0))))
      (.pi (.sigma ground (.var 1)) (.sigma (.var 1) ground)) := by
  have pairs : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.sigma (.var 1) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 1) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have q : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.var 0) (.sigma ground (.var 2)) :=
    Derivable.var 0
  have body : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1)))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma (.var 1) ground) :=
    .pairIntro pairs (.sort _) (.sndElim q) (.fstElim q)
  have innerFormed : Typed Tower.rules (.snoc Γ U0) (.pi (.sigma ground (.var 1)) (.sigma (.var 1) ground)) U0 :=
    .cumul (.piForm (tBody_typed Γ) (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  exact .lamIntro innerFormed (.sort _) body

/-- The frame `X : U0, p : S X`. -/
abbrev roundFrame {n : Nat} (Γ : Tower.Ctx n) : Tower.Ctx (n + 2) := .snoc (.snoc Γ U0) (.sigma (.var 0) ground)

/-- **The round trip is the identity in the knowledge**: `swapBack X (swap X p)` is `p`, by β and
pair η. So the evidence of `Run` is an equivalence of `S X` and `T X`, not only a pair of maps. -/
theorem swap_round_trip {n : Nat} (Γ : Tower.Ctx n) :
    Equal Tower.rules (roundFrame Γ)
      (.app (.app swapCode (.var 1)) (.app (.app swapCode (.var 1)) (.var 0))) (.var 0) (.sigma (.var 1) ground) := by
  have tX : Typed Tower.rules (roundFrame Γ) (.var 1) U0 := Derivable.var 1
  have p : Typed Tower.rules (roundFrame Γ) (.var 0) (.sigma (.var 1) ground) := Derivable.var 0
  have sFormed : Typed Tower.rules (roundFrame Γ) (.sigma (.var 1) ground) U0 :=
    .cumul (.sigmaForm tX (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have tFormed : Typed Tower.rules (roundFrame Γ) (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
  -- `swap X p` is `(snd p, fst p)`
  have swapX := Derivable.betaPi (swapType_formed _) (.sort _) (swapInner_typed _) tX
  have step1 := Derivable.appCong swapX (Derivable.refl p)
  have fwdPairs : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma (.var 1) ground)) (.sigma ground (.var 3)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 3) (.sort _) (.sorts _ _)) collapse
  have pp : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma (.var 1) ground)) (.var 0) (.sigma (.var 2) ground) :=
    Derivable.var 0
  have fwdBody : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma (.var 1) ground))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 3)) :=
    .pairIntro fwdPairs (.sort _) (.sndElim pp) (.fstElim pp)
  have fwdFormed : Typed Tower.rules (roundFrame Γ) (.pi (.sigma (.var 1) ground) (.sigma ground (.var 3))) U0 :=
    .cumul (.piForm sFormed (.sort _) fwdPairs (.sort _) (.sorts _ _)) collapse
  have step2 := Derivable.betaPi fwdFormed (.sort _) fwdBody p
  have forward : Equal Tower.rules (roundFrame Γ) (.app (.app swapCode (.var 1)) (.var 0))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 2)) := .trans step1 step2
  -- `swapBack X (snd p, fst p)` is `(fst p, snd p)`
  have swapBackX := Derivable.betaPi (swapBackType_formed _) (.sort _) (swapBackInner_typed _) tX
  have step3 := Derivable.appCong swapBackX forward
  have bwdPairs : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma ground (.var 2))) (.sigma (.var 2) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 2) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have qq : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma ground (.var 2))) (.var 0) (.sigma ground (.var 3)) :=
    Derivable.var 0
  have bwdBody : Typed Tower.rules (.snoc (roundFrame Γ) (.sigma ground (.var 2)))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma (.var 2) ground) :=
    .pairIntro bwdPairs (.sort _) (.sndElim qq) (.fstElim qq)
  have bwdFormed : Typed Tower.rules (roundFrame Γ) (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground)) U0 :=
    .cumul (.piForm tFormed (.sort _) bwdPairs (.sort _) (.sorts _ _)) collapse
  have swappedP : Typed Tower.rules (roundFrame Γ) (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 2)) :=
    .pairIntro tFormed (.sort _) (.sndElim p) (.fstElim p)
  have step4 := Derivable.betaPi bwdFormed (.sort _) bwdBody swappedP
  have step5 := Derivable.pairCong sFormed (.sort _)
    (Derivable.betaSnd tFormed (.sort _) (.sndElim p) (.fstElim p))
    (Derivable.betaFst tFormed (.sort _) (.sndElim p) (.fstElim p))
  -- `(fst p, snd p)` is `p`, by pair η
  have rebuilt : Typed Tower.rules (roundFrame Γ) (.pair (.fst (.var 0)) (.snd (.var 0))) (.sigma (.var 1) ground) :=
    .pairIntro sFormed (.sort _) (.fstElim p) (.sndElim p)
  have step6 := Derivable.etaSigma rebuilt p (Derivable.betaFst sFormed (.sort _) (.fstElim p) (.sndElim p))
    (Derivable.betaSnd sFormed (.sort _) (.fstElim p) (.sndElim p))
  exact .trans step3 (.trans step4 (.trans step5 step6))

/-- **The round trip has a `refl` witness**: `refl p : Id (S X) (swapBack X (swap X p)) p`. -/
theorem round_trip_witness {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (roundFrame Γ) (.refl (.var 0))
      (.id (.sigma (.var 1) ground) (.app (.app swapCode (.var 1)) (.app (.app swapCode (.var 1)) (.var 0)))
        (.var 0)) := by
  have p : Typed Tower.rules (roundFrame Γ) (.var 0) (.sigma (.var 1) ground) := Derivable.var 0
  have sFormed : Typed Tower.rules (roundFrame Γ) (.sigma (.var 1) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 1) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have same : Equal Tower.rules (roundFrame Γ) (.id (.sigma (.var 1) ground) (.var 0) (.var 0))
      (.id (.sigma (.var 1) ground) (.app (.app swapCode (.var 1)) (.app (.app swapCode (.var 1)) (.var 0))) (.var 0))
      U0 :=
    .idCong (.refl sFormed) (.sort _) (.symm (swap_round_trip Γ)) (.refl p)
  exact .conv (.reflIntro p) same (.sort _)

end EqualityOnTheStep.Computation

#print axioms EqualityOnTheStep.Computation.swapInner_typed
#print axioms EqualityOnTheStep.Computation.coercion_computes
#print axioms EqualityOnTheStep.Computation.transported_member_computes
#print axioms EqualityOnTheStep.Computation.swap_round_trip
#print axioms EqualityOnTheStep.Computation.round_trip_witness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
