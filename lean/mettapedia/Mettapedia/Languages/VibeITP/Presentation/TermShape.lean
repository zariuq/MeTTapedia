import Mettapedia.Languages.VibeITP.Presentation.SpecFacts

/-!
# Signature and arity profiles for kernel operations

Term operations traverse applications at the arity declared by their head.
This structural profile leaves bound-variable indices and literal lengths
unbounded; the operation itself checks the word arithmetic it performs.
Kernel formation implies the profile. The distinction also applies to
definition-generated eta terms in theories with unrestricted natural arities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

mutual
inductive TermShape (sig : Sig) : Term → Prop where
  | bvar (i : Nat) : TermShape sig (.bvar i)
  | lit (bs : List UInt8) : TermShape sig (.lit bs)
  | app {s : SymId} {info : SymInfo} {args : List Term} :
      sig s = some info → args.length = info.arity → TermShapeList sig args →
        TermShape sig (.app s args)

inductive TermShapeList (sig : Sig) : List Term → Prop where
  | nil : TermShapeList sig []
  | cons {t : Term} {ts : List Term} :
      TermShape sig t → TermShapeList sig ts → TermShapeList sig (t :: ts)
end

theorem TermShape.app_iff {sig : Sig} {s : SymId} {args : List Term} :
    TermShape sig (.app s args) ↔
      ∃ info, sig s = some info ∧ args.length = info.arity ∧ TermShapeList sig args := by
  constructor
  · intro h
    cases h with
    | app hs hlen hargs => exact ⟨_, hs, hlen, hargs⟩
  · rintro ⟨info, hs, hlen, hargs⟩
    exact .app hs hlen hargs

theorem TermShapeList.cons_iff {sig : Sig} {t : Term} {ts : List Term} :
    TermShapeList sig (t :: ts) ↔ TermShape sig t ∧ TermShapeList sig ts := by
  constructor
  · intro h
    cases h with
    | cons ht hts => exact ⟨ht, hts⟩
  · rintro ⟨ht, hts⟩
    exact .cons ht hts

mutual
theorem wellFormed_termShape (sig : Sig) (t : Term)
    (h : WellFormed sig t = true) : TermShape sig t := by
  cases t with
  | bvar i => exact .bvar i
  | lit bs => exact .lit bs
  | app s args =>
      cases hs : sig s with
      | none => simp [WellFormed, hs] at h
      | some info =>
          have hw : args.length = info.arity ∧ WellFormedList sig args = true := by
            simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using h
          exact .app hs hw.1 (wellFormedList_termShape sig args hw.2)
termination_by sizeOf t

theorem wellFormedList_termShape (sig : Sig) (ts : List Term)
    (h : WellFormedList sig ts = true) : TermShapeList sig ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
      have hw : WellFormed sig t = true ∧ WellFormedList sig ts = true := by
        simpa only [WellFormedList, Bool.and_eq_true] using h
      exact .cons (wellFormed_termShape sig t hw.1) (wellFormedList_termShape sig ts hw.2)
termination_by sizeOf ts
end

theorem TermShapeList.of_mem {sig : Sig} {ts : List Term}
    (h : TermShapeList sig ts) {t : Term} (ht : t ∈ ts) : TermShape sig t := by
  cases ts with
  | nil => simp at ht
  | cons head tail =>
      obtain ⟨hhead, htail⟩ := TermShapeList.cons_iff.mp h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hhead
      · exact TermShapeList.of_mem htail ht
termination_by ts.length

end Mettapedia.Languages.VibeITP.Presentation
