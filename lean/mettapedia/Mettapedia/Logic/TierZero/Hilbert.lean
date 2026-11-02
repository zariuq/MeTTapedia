import Mettapedia.Logic.TierZero.Kernel
import Mettapedia.Logic.PropositionalHilbertChecking

/-!
# A presentation proved adequate: Foundation's Hilbert calculi on the tier-0 kernel

The intuitionistic and classical Hilbert calculi of the Foundation library
(`Hilbert.Standard`, through `PropositionalHilbertChecking.Source`) become presentations of the
tier-0 kernel: a rule name and its explicit arguments give the instance, as the MeTTa kernel reads
`(rule mp ($a $b) ((|- (-> $a $b)) (|- $a)) (|- $b))` with ground arguments. Excluded middle is a
rule of the classical presentation only. The source relation is the library's own, defined
without reference to this kernel.

* `derivable_iff_source`: kernel derivability is exactly the source's provability.
* `accepts_iff_source`: a proof accepted by the kernel's checker exists exactly for the source's
  theorems (the kernel's native proof type is inhabited exactly at the source's theorems).
* `machine_accepts_iff_source`: the same for the step machine of `tier0_seq.metta`.

## Controls

`Controls`: the identity proof (S, K, K, MP, MP) is accepted; excluded middle is accepted
classically and refused intuitionistically; a proof whose last `mp` cites its premises in the wrong
order is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Hilbert

open Mettapedia.Logic
open Mettapedia.Logic.PropositionalHilbertChecking

/-- The rule names of the presentation. -/
inductive Name where
  | truth | k | s | andLeft | andRight | andIntro | orLeft | orRight | orElim | explosion
  | excludedMiddle | mp
  deriving DecidableEq, Repr

/-- A rule name with its explicit arguments, as a code of the source's rule instances. -/
def toCode : Name → List Formula → Option Code
  | .truth, [] => some .truth
  | .k, [a, b] => some (.k a b)
  | .s, [a, b, c] => some (.s a b c)
  | .andLeft, [a, b] => some (.andLeft a b)
  | .andRight, [a, b] => some (.andRight a b)
  | .andIntro, [a, b] => some (.andIntro a b)
  | .orLeft, [a, b] => some (.orLeft a b)
  | .orRight, [a, b] => some (.orRight a b)
  | .orElim, [a, b, c] => some (.orElim a b c)
  | .explosion, [a] => some (.explosion a)
  | .excludedMiddle, [a] => some (.excludedMiddle a)
  | .mp, [a, b] => some (.mp a b)
  | _, _ => none

/-- The presentation of a profile: excluded middle is admitted only classically. -/
def presentation (profile : Profile) : Presentation.{0} where
  J := Formula
  R := Name
  A := List Formula
  inst r args :=
    match toCode r args with
    | none => none
    | some code => if code.allowed profile then some (code.premises, code.conclusion) else none
  side _ := false

instance (profile : Profile) : DecidableEq (presentation profile).J :=
  inferInstanceAs (DecidableEq Formula)

theorem inst_rule {profile : Profile} {r : Name} {args : List Formula} {ps : List Formula}
    {c : Formula} (h : (presentation profile).inst r args = some (ps, c)) : Rule profile ps c := by
  simp only [presentation] at h
  cases hc : toCode r args with
  | none => simp [hc] at h
  | some code =>
      simp only [hc] at h
      by_cases ha : code.allowed profile = true
      · simp only [ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact code.rule profile ha
      · simp [ha] at h

theorem rule_inst {profile : Profile} {ps : List Formula} {c : Formula} (rule : Rule profile ps c) :
    ∃ r args, (presentation profile).inst r args = some (ps, c) := by
  cases rule with
  | truth => exact ⟨.truth, [], rfl⟩
  | k a b => exact ⟨.k, [a, b], rfl⟩
  | s a b c => exact ⟨.s, [a, b, c], rfl⟩
  | andLeft a b => exact ⟨.andLeft, [a, b], rfl⟩
  | andRight a b => exact ⟨.andRight, [a, b], rfl⟩
  | andIntro a b => exact ⟨.andIntro, [a, b], rfl⟩
  | orLeft a b => exact ⟨.orLeft, [a, b], rfl⟩
  | orRight a b => exact ⟨.orRight, [a, b], rfl⟩
  | orElim a b c => exact ⟨.orElim, [a, b, c], rfl⟩
  | explosion a => exact ⟨.explosion, [a], rfl⟩
  | excludedMiddle classical a =>
      subst classical
      exact ⟨.excludedMiddle, [a], rfl⟩
  | mp a => exact ⟨.mp, [a, c], rfl⟩

theorem derives_derivable {profile : Profile} {φ : Formula} (h : Derives (Rule profile) φ) :
    Derivable (presentation profile) [] φ := by
  induction h with
  | node premises conclusion rule _ ih =>
      obtain ⟨r, args, hi⟩ := rule_inst rule
      exact Derivable.rule hi fun p mem _ => ih p mem

/-- **Adequacy**: derivability in the kernel's presentation is the source's provability. -/
theorem derivable_source {profile : Profile} {hyps : List (presentation profile).J}
    {φ : (presentation profile).J} (h : Derivable (presentation profile) hyps φ)
    (hypsOk : ∀ j ∈ hyps, Source profile j) : Source profile φ := by
  induction h with
  | hyp mem => exact hypsOk _ mem
  | rule hi _ ih => exact rule_source profile (inst_rule hi) fun p mem => ih p mem rfl

theorem derivable_iff_source (profile : Profile) (φ : Formula) :
    Derivable (presentation profile) [] φ ↔ Source profile φ :=
  ⟨fun h => derivable_source h (by simp),
   fun h => derives_derivable ((source_iff_derives profile φ).mp h)⟩

/-- **Adequacy of checking**: the kernel accepts a proof of `φ` exactly when `φ` is a theorem of the
source calculus. -/
theorem accepts_iff_source (profile : Profile) (φ : Formula) :
    (∃ proof root, check (P := presentation profile) [] proof root φ = true) ↔ Source profile φ :=
  (check_iff_derivable (P := presentation profile) [] φ).trans (derivable_iff_source profile φ)

/-- The same for the step machine. -/
theorem machine_accepts_iff_source (profile : Profile) (φ : Formula) :
    (∃ proof root s, Relation.ReflTransGen (Step (P := presentation profile) [])
        ⟨[], none, proof⟩ s ∧ Accepting [] root φ s) ↔ Source profile φ := by
  rw [← accepts_iff_source]
  constructor
  · rintro ⟨proof, root, s, reach, acc⟩
    exact ⟨proof, root, (reaches_accept_iff_check [] proof root φ).mp ⟨s, reach, acc⟩⟩
  · rintro ⟨proof, root, h⟩
    obtain ⟨s, reach, acc⟩ := (reaches_accept_iff_check [] proof root φ).mpr h
    exact ⟨proof, root, s, reach, acc⟩

namespace Controls

def p : Formula := .atom 0
def q : Formula := .atom 1

/-- `p → p`: S, K, K, then two MP steps (Metamath's `id` shape). -/
def idProof : List (Node (presentation .intuitionistic)) :=
  [ (Name.s, [p, .imp p p, p], []),
    (Name.k, [p, .imp p p], []),
    (Name.mp, [.imp p (.imp (.imp p p) p),
               .imp (.imp p (.imp p p)) (.imp p p)], [Kid.node 0, Kid.node 1]),
    (Name.k, [p, p], []),
    (Name.mp, [.imp p (.imp p p), .imp p p], [Kid.node 2, Kid.node 3]) ]

theorem id_accepted : check (P := presentation .intuitionistic) [] idProof (.node 4) (.imp p p) = true := by
  decide

/-- The same nodes with the children of the last `mp` swapped: refused. -/
def idSwapped : List (Node (presentation .intuitionistic)) :=
  [ (Name.s, [p, .imp p p, p], []),
    (Name.k, [p, .imp p p], []),
    (Name.mp, [.imp p (.imp (.imp p p) p),
               .imp (.imp p (.imp p p)) (.imp p p)], [Kid.node 0, Kid.node 1]),
    (Name.k, [p, p], []),
    (Name.mp, [.imp p (.imp p p), .imp p p], [Kid.node 3, Kid.node 2]) ]

theorem id_swapped_refused :
    check (P := presentation .intuitionistic) [] idSwapped (.node 4) (.imp p p) = false := by
  decide

/-- Excluded middle: one node. -/
def emProof (profile : Profile) : List (Node (presentation profile)) := [(Name.excludedMiddle, [p], [])]

theorem em_classical :
    check (P := presentation .classical) [] (emProof .classical) (.node 0) (.or p (.imp p .falsum)) = true := by
  decide

theorem em_refused_intuitionistically :
    check (P := presentation .intuitionistic) [] (emProof .intuitionistic) (.node 0)
      (.or p (.imp p .falsum)) = false := by
  decide

end Controls

end Mettapedia.Logic.TierZero.Hilbert
