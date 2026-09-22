import Mettapedia.GSLT.Logic.PropositionalMLL
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.GSLT.Core.InteractionEvent

/-!
# Session processes for propositional MLL

Processes carry channel names; their steps are the principal cut reductions,
one communication per reduction. Erasing the names sends a process to the
untyped MLL proof term of `PropositionalMLL`, and every communication erases
to exactly one `CutStep`.

The correspondence covers *normalisation* of a proof that is already found.
It says nothing about proof search: a search that may deadlock, diverge or
resolve nondeterministically is outside the session-typed reading.

Renaming is the structural replacement of one channel name by another. This
fragment identifies channels syntactically and does not model α-conversion.

Two negative results bound the connection:

* `no_binary_residual_for_comm` — the multiplicative contractum keeps all
  three components of its redex, so it is not of `SoundCut` shape, whose
  residual is a function of the two continuations alone. The interaction
  layer does fit: `sessionSite` presents the communications as
  `Type`-valued occurrence evidence.
* `no_cover_along_name_erasure` — name erasure is a translation but not a
  cover. A typed process can have a cut whose proof term is a redex while
  the process has no communication, because the proof term does not record
  which occurrence of the cut formula each rule introduced; on the process
  side that cut needs a commuting conversion first. Hennessy--Milner
  adequacy therefore does not transport along this erasure. A cover would
  need an occurrence-indexed target, or commuting conversions admitted as
  steps, which this fragment deliberately excludes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.MLLSession

open Mettapedia.GSLT
open Mettapedia.GSLT.Logic.PropositionalMLL

abbrev Name := Nat

/-- Multiplicative session processes. `out` sends a fresh name, `inp`
receives one, and `cut` is the annotated parallel composition with a private
channel. -/
inductive Proc where
  | link (x w : Name) (n : Nat)
  | close (x : Name)
  | wait (x : Name) (P : Proc)
  | out (x y : Name) (P Q : Proc)
  | inp (x y : Name) (P : Proc)
  | cut (x : Name) (A : Formula) (P Q : Proc)
deriving DecidableEq

/-- Replace the channel name `a` by `b` everywhere. -/
def renameProc (a b : Name) : Proc → Proc
  | .link x w n => .link (if x = a then b else x) (if w = a then b else w) n
  | .close x => .close (if x = a then b else x)
  | .wait x P => .wait (if x = a then b else x) (renameProc a b P)
  | .out x y P Q =>
      .out (if x = a then b else x) (if y = a then b else y)
        (renameProc a b P) (renameProc a b Q)
  | .inp x y P =>
      .inp (if x = a then b else x) (if y = a then b else y) (renameProc a b P)
  | .cut x A P Q =>
      .cut (if x = a then b else x) A (renameProc a b P) (renameProc a b Q)

/-! ## Communication is principal cut reduction

Each rule mirrors one constructor of `PropositionalMLL.CutStep`, with the
channel names that the proof term does not record.
-/

inductive SessionStep : Proc → Proc → Prop where
  | axLeft (x w : Name) (n : Nat) (P : Proc) :
      SessionStep (.cut x (.atom n) (.link w x n) P) (renameProc x w P)
  | axLeftFlip (x w : Name) (n : Nat) (P : Proc) :
      SessionStep (.cut x (.atom n) (.link x w n) P) (renameProc x w P)
  | axRight (x w : Name) (n : Nat) (P : Proc) :
      SessionStep (.cut x (.natom n) P (.link w x n)) (renameProc x w P)
  | axRightFlip (x w : Name) (n : Nat) (P : Proc) :
      SessionStep (.cut x (.natom n) P (.link x w n)) (renameProc x w P)
  | unitLeft (x : Name) (P : Proc) :
      SessionStep (.cut x .one (.close x) (.wait x P)) P
  | unitRight (x : Name) (P : Proc) :
      SessionStep (.cut x .bot (.wait x P) (.close x)) P
  | comm (x y z : Name) (A B : Formula) (P Q R : Proc) :
      SessionStep
        (.cut x (.tensor A B) (.out x y P Q) (.inp x z R))
        (.cut y A P (.cut x B Q (renameProc z y R)))
  | commSwap (x y z : Name) (A B : Formula) (R P Q : Proc) :
      SessionStep
        (.cut x (.par A B) (.inp x y R) (.out x z P Q))
        (.cut x B (.cut y A R (renameProc z y P)) Q)

def sessionGSLT : GSLT where
  Term := Proc
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SessionStep
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

/-! ## Erasing the names -/

/-- Forget channel names: a process becomes an untyped MLL proof term. -/
def toProof : Proc → Proof
  | .link _ _ n => .ax n
  | .close _ => .oneIntro
  | .wait _ P => .botIntro (toProof P)
  | .out _ _ P Q => .tensorIntro (toProof P) (toProof Q)
  | .inp _ _ P => .parIntro (toProof P)
  | .cut _ A P Q => .cut A (toProof P) (toProof Q)

@[simp] theorem toProof_rename (a b : Name) (P : Proc) :
    toProof (renameProc a b P) = toProof P := by
  induction P with
  | link x w n => rfl
  | close x => rfl
  | wait x P ih => simp [renameProc, toProof, ih]
  | out x y P Q ihP ihQ => simp [renameProc, toProof, ihP, ihQ]
  | inp x y P ih => simp [renameProc, toProof, ih]
  | cut x A P Q ihP ihQ => simp [renameProc, toProof, ihP, ihQ]

/-- **One communication erases to one cut reduction.** -/
theorem toProof_step {S T : Proc} (h : SessionStep S T) :
    CutStep (toProof S) (toProof T) := by
  cases h with
  | axLeft a b n U =>
      simpa [toProof] using CutStep.axLeft n (toProof U)
  | axLeftFlip a b n U =>
      simpa [toProof] using CutStep.axLeft n (toProof U)
  | axRight a b n U =>
      simpa [toProof] using CutStep.axRight n (toProof U)
  | axRightFlip a b n U =>
      simpa [toProof] using CutStep.axRight n (toProof U)
  | unitLeft a =>
      simp only [toProof]
      exact CutStep.oneBot _
  | unitRight a =>
      simp only [toProof]
      exact CutStep.botOne _
  | comm a b c A B U V W =>
      simpa [toProof] using
        CutStep.tensorPar A B (toProof U) (toProof V) (toProof W)
  | commSwap a b c A B W U V =>
      simpa [toProof] using
        CutStep.parTensor A B (toProof W) (toProof U) (toProof V)

/-- Name erasure is a forward operational translation of rewrite theories. -/
def eraseNames :
    Mettapedia.GSLT.IndexedOperational.OperationalTranslation sessionGSLT mllCutGSLT where
  mapTerm := toProof
  mapEquiv := by
    intro left right equivalent
    exact congrArg toProof equivalent
  mapStep := by
    intro source target step
    exact toProof_step step

/-! ## Positive and negative controls -/

/-- Positive: a principal tensor/par cut is exactly one communication, and it
erases to the single `tensorPar` redex. -/
theorem comm_is_one_communication (x y z : Name) (A B : Formula) (P Q R : Proc) :
    SessionStep
        (.cut x (.tensor A B) (.out x y P Q) (.inp x z R))
        (.cut y A P (.cut x B Q (renameProc z y R))) ∧
      CutStep
        (toProof (.cut x (.tensor A B) (.out x y P Q) (.inp x z R)))
        (toProof (.cut y A P (.cut x B Q (renameProc z y R)))) :=
  ⟨SessionStep.comm x y z A B P Q R,
    toProof_step (SessionStep.comm x y z A B P Q R)⟩

/-- Negative: a cut whose two premises are both outputs is a commuting
conversion, not a communication. It takes no session step. -/
theorem commuting_conversion_is_not_a_communication
    (x y : Name) (A B : Formula) (P Q P' Q' : Proc) :
    ¬ ∃ T : Proc,
        SessionStep (.cut x (.tensor A B) (.out x y P Q) (.out x y P' Q')) T := by
  rintro ⟨T, hstep⟩
  cases hstep

/-! ## Why this cut is not a `SoundCut`

`InteractionEvent.SoundCut` requires the contractum to be a function of the
two continuations alone: `residual body payload`. The multiplicative
contractum keeps all three components of the redex, so no such function
exists.
-/

/-- The contractum of a communication is determined by the redex. -/
theorem comm_target_unique {x y z : Name} {A B : Formula} {P Q R T : Proc}
    (h : SessionStep (.cut x (.tensor A B) (.out x y P Q) (.inp x z R)) T) :
    T = .cut y A P (.cut x B Q (renameProc z y R)) := by
  cases h
  rfl

theorem no_binary_residual_for_comm :
    ¬ ∃ residual : Proc → Proc → Proc,
        ∀ (x y : Name) (A B : Formula) (P Q R : Proc),
          SessionStep
            (.cut x (.tensor A B) (.out x y P Q) (.inp x y R))
            (residual R Q) := by
  rintro ⟨residual, hres⟩
  have h0 :=
    comm_target_unique (hres 0 1 .one .one (.close 0) (.close 2) (.close 3))
  have h1 :=
    comm_target_unique (hres 0 1 .one .one (.close 1) (.close 2) (.close 3))
  exact absurd (h0.symm.trans h1) (by decide)

/-! ## Typing: one-sided MLL over named channels

Contexts are linear lists of named formulas. Each rule is the MLL rule of
`PropositionalMLL.Derives` with the channel that carries the formula.
-/

inductive Typed : List (Name × Formula) → Proc → Type where
  | link (x w : Name) (n : Nat) :
      Typed [(x, .atom n), (w, .natom n)] (.link x w n)
  | close (x : Name) : Typed [(x, .one)] (.close x)
  | wait {Γ : List (Name × Formula)} {P : Proc} (x : Name) :
      Typed Γ P → Typed ((x, .bot) :: Γ) (.wait x P)
  | out {Γ Δ : List (Name × Formula)} {A B : Formula} {P Q : Proc} (x y : Name) :
      Typed ((y, A) :: Γ) P → Typed ((x, B) :: Δ) Q →
        Typed ((x, .tensor A B) :: (Γ ++ Δ)) (.out x y P Q)
  | inp {Γ : List (Name × Formula)} {A B : Formula} {P : Proc} (x y : Name) :
      Typed ((y, A) :: (x, B) :: Γ) P → Typed ((x, .par A B) :: Γ) (.inp x y P)
  | cut {Γ Δ : List (Name × Formula)} {A : Formula} {P Q : Proc} (x : Name) :
      Typed ((x, A) :: Γ) P → Typed ((x, dual A) :: Δ) Q →
        Typed (Γ ++ Δ) (.cut x A P Q)
  | ex {Γ Δ : List (Name × Formula)} {P : Proc} :
      Typed Γ P → Γ.Perm Δ → Typed Δ P

/-- **Typing is one-sided MLL over channels:** dropping the names sends a
typing derivation to a derivation of the same sequent. -/
def eraseTyped : {Γ : List (Name × Formula)} → {P : Proc} → Typed Γ P →
    Derives (Γ.map Prod.snd)
  | _, _, .link _ _ n => Derives.ax n
  | _, _, .close _ => Derives.one
  | _, _, .wait _ d => Derives.bot (eraseTyped d)
  | _, _, .out _ _ dp dq => by
      simpa [List.map_append] using Derives.tensor (eraseTyped dp) (eraseTyped dq)
  | _, _, .inp _ _ d => Derives.par (eraseTyped d)
  | _, _, .cut _ dp dn => by
      simpa [List.map_append] using Derives.cut (eraseTyped dp) (eraseTyped dn)
  | _, _, .ex d perm => Derives.ex (eraseTyped d) (List.Perm.map Prod.snd perm)

/-! ## Name erasure is a translation but not a cover

A proof term does not record which occurrence of the cut formula each rule
introduced. A typed process can therefore have a cut whose proof term is a
redex while the process itself has no communication: the `⊥` that the proof
term matches was introduced deeper inside, on another channel.
-/

/-- `⊢ v:⊥, z:1`. The cut is on `x:1`, and the `⊥` the proof term matches is
introduced by the inner `wait` on `x`, not by the outer one on `v`. -/
def gapProc (x v z : Name) : Proc :=
  .cut x .one (.close x) (.wait v (.wait x (.close z)))

def gapTyped (x v z : Name) : Typed [(v, .bot), (z, .one)] (gapProc x v z) :=
  Typed.cut (Γ := []) x (Typed.close x)
    (Typed.ex
      (Typed.wait v (Typed.wait x (Typed.close z)))
      (List.Perm.swap (x, Formula.bot) (v, Formula.bot) [(z, Formula.one)]))

theorem gap_image_steps (x v z : Name) :
    CutStep (toProof (gapProc x v z)) (.botIntro .oneIntro) := by
  simpa [gapProc, toProof] using
    CutStep.oneBot (Proof.botIntro Proof.oneIntro)

theorem gap_has_no_session_step (x v z : Name) (hxv : x ≠ v) :
    ¬ ∃ T : Proc, SessionStep (gapProc x v z) T := by
  rintro ⟨T, h⟩
  simp only [gapProc] at h
  cases h with
  | unitLeft a => exact absurd rfl hxv

/-- The counterexample is typed, its proof term steps, and the process does
not. So name erasure is not a cover, and Hennessy--Milner adequacy does not
transport along it. -/
theorem erasure_gap :
    Nonempty (Typed [(1, .bot), (2, .one)] (gapProc 0 1 2)) ∧
      CutStep (toProof (gapProc 0 1 2)) (.botIntro .oneIntro) ∧
      ¬ ∃ T : Proc, SessionStep (gapProc 0 1 2) T :=
  ⟨⟨gapTyped 0 1 2⟩, gap_image_steps 0 1 2,
    gap_has_no_session_step 0 1 2 (by decide)⟩

theorem no_cover_along_name_erasure :
    ¬ ∃ c : Mettapedia.GSLT.IndexedOperational.SemanticCoveredTranslation
        sessionGSLT mllCutGSLT, c.mapTerm = toProof := by
  rintro ⟨c, hc⟩
  have hstep : mllCutGSLT.Step (c.mapTerm (gapProc 0 1 2)) (.botIntro .oneIntro) := by
    rw [hc]
    exact gap_image_steps 0 1 2
  obtain ⟨target, hsess, -⟩ := c.liftStep hstep
  exact gap_has_no_session_step 0 1 2 (by decide) ⟨target, hsess⟩

/-! ## Communications as interaction events

`SoundCut` does not fit (`no_binary_residual_for_comm`), but the interaction
layer does: each communication kind is a named site, and the redex itself is
the occurrence evidence. Evidence is `Type`-valued, so two communications at
the same endpoints stay distinct.
-/

inductive CommKind where
  | link
  | unit
  | multiplicative
deriving DecidableEq

/-- Occurrence evidence for one communication, indexed by its kind. -/
inductive SessionRedex : CommKind → Proc → Proc → Type where
  | axLeft (x w : Name) (n : Nat) (P : Proc) :
      SessionRedex .link (.cut x (.atom n) (.link w x n) P) (renameProc x w P)
  | axLeftFlip (x w : Name) (n : Nat) (P : Proc) :
      SessionRedex .link (.cut x (.atom n) (.link x w n) P) (renameProc x w P)
  | axRight (x w : Name) (n : Nat) (P : Proc) :
      SessionRedex .link (.cut x (.natom n) P (.link w x n)) (renameProc x w P)
  | axRightFlip (x w : Name) (n : Nat) (P : Proc) :
      SessionRedex .link (.cut x (.natom n) P (.link x w n)) (renameProc x w P)
  | unitLeft (x : Name) (P : Proc) :
      SessionRedex .unit (.cut x .one (.close x) (.wait x P)) P
  | unitRight (x : Name) (P : Proc) :
      SessionRedex .unit (.cut x .bot (.wait x P) (.close x)) P
  | comm (x y z : Name) (A B : Formula) (P Q R : Proc) :
      SessionRedex .multiplicative
        (.cut x (.tensor A B) (.out x y P Q) (.inp x z R))
        (.cut y A P (.cut x B Q (renameProc z y R)))
  | commSwap (x y z : Name) (A B : Formula) (R P Q : Proc) :
      SessionRedex .multiplicative
        (.cut x (.par A B) (.inp x y R) (.out x z P Q))
        (.cut x B (.cut y A R (renameProc z y P)) Q)

/-- Occurrence evidence authorises exactly its own communication. -/
theorem redexStep {k : CommKind} {S T : Proc} : SessionRedex k S T → SessionStep S T
  | .axLeft x w n P => SessionStep.axLeft x w n P
  | .axLeftFlip x w n P => SessionStep.axLeftFlip x w n P
  | .axRight x w n P => SessionStep.axRight x w n P
  | .axRightFlip x w n P => SessionStep.axRightFlip x w n P
  | .unitLeft x P => SessionStep.unitLeft x P
  | .unitRight x P => SessionStep.unitRight x P
  | .comm x y z A B P Q R => SessionStep.comm x y z A B P Q R
  | .commSwap x y z A B R P Q => SessionStep.commSwap x y z A B R P Q

/-- The communication sites of the session fragment. -/
def sessionSite :
    Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation sessionGSLT where
  Site := CommKind
  Event := SessionRedex
  sound := by
    intro site source target event
    exact redexStep event

/-- The session fragment with its sites named: an interactive theory whose
site erasure is the bare rewrite theory. -/
def sessionInteractive :
    Mettapedia.GSLT.Core.InteractionEvent.Interactive :=
  { theory := sessionGSLT, site := sessionSite }

@[simp] theorem sessionInteractive_erase :
    sessionInteractive.erase = sessionGSLT :=
  rfl

/-- Positive: the multiplicative communication is an enabled event at its
site, and erasing the event returns the same step. -/
theorem multiplicative_event_is_enabled
    (x y z : Name) (A B : Formula) (P Q R : Proc) :
    sessionGSLT.Step
        (.cut x (.tensor A B) (.out x y P Q) (.inp x z R))
        (.cut y A P (.cut x B Q (renameProc z y R))) :=
  redexStep (SessionRedex.comm x y z A B P Q R)

#print axioms toProof_rename
#print axioms toProof_step
#print axioms eraseNames
#print axioms comm_is_one_communication
#print axioms commuting_conversion_is_not_a_communication
#print axioms comm_target_unique
#print axioms no_binary_residual_for_comm
#print axioms eraseTyped
#print axioms gapTyped
#print axioms erasure_gap
#print axioms no_cover_along_name_erasure
#print axioms redexStep
#print axioms sessionSite
#print axioms multiplicative_event_is_enabled

end Mettapedia.GSLT.Logic.MLLSession
