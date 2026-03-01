import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# MORK Match Specification

Relational specification for `matchAtom` on the currently supported MORK
fragment (variables, symbols, grounded values).  This isolates the matching
semantics from implementation details and makes the supported scope explicit.

Expression-pattern matching is intentionally unsupported in `matchAtom` today.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.OSLF.MeTTaCore (Atom GroundedValue)

/-- Relational spec for one-step atom matching in the supported fragment. -/
inductive MatchAtomRel : Subst → Atom → Atom → Subst → Prop where
  /-- Fresh variable bind. -/
  | var_fresh {σ : Subst} {v : String} {a : Atom}
      (hlookup : σ.lookup v = none) :
      MatchAtomRel σ (.var v) a ((v, a) :: σ)
  /-- Already-bound variable must match the same atom. -/
  | var_bound {σ : Subst} {v : String} {a : Atom}
      (hlookup : σ.lookup v = some a) :
      MatchAtomRel σ (.var v) a σ
  /-- Symbols match only identical symbols. -/
  | symbol {σ : Subst} {s : String} :
      MatchAtomRel σ (.symbol s) (.symbol s) σ
  /-- Grounded values match only identical grounded values. -/
  | grounded {σ : Subst} {g : GroundedValue} :
      MatchAtomRel σ (.grounded g) (.grounded g) σ

/-- Current `matchAtom` intentionally does not handle expression patterns. -/
theorem matchAtom_expression_pattern_none (σ : Subst) (es : List Atom) (conc : Atom) :
    matchAtom σ (.expression es) conc = none := by
  cases conc <;> rfl

/-- Soundness of executable `matchAtom` w.r.t. `MatchAtomRel`. -/
theorem matchAtom_sound {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    MatchAtomRel σ pat conc σ' := by
  cases pat with
  | var v =>
      simp only [matchAtom] at h
      cases hlookup : σ.lookup v with
      | none =>
          simp [hlookup] at h
          cases h
          exact MatchAtomRel.var_fresh hlookup
      | some a =>
          by_cases heq : conc == a
          · simp [hlookup, heq] at h
            cases h
            have hca : conc = a := Atom.eq_of_beq_eq_true (by simpa using heq)
            subst hca
            exact MatchAtomRel.var_bound hlookup
          · simp [hlookup, heq] at h
  | symbol s =>
      cases conc with
      | symbol t =>
          by_cases heq : s == t
          · simp [matchAtom, heq] at h
            cases h
            have hst : s = t := by
              have hatom : ((Atom.symbol s : Atom) == (Atom.symbol t : Atom)) = true := by
                simpa [BEq.beq, Atom.beq] using heq
              have heqAtom : (Atom.symbol s : Atom) = (Atom.symbol t : Atom) :=
                Atom.eq_of_beq_eq_true hatom
              cases heqAtom
              rfl
            subst hst
            exact MatchAtomRel.symbol
          · simp [matchAtom, heq] at h
      | var _ => simp [matchAtom] at h
      | grounded _ => simp [matchAtom] at h
      | expression _ => simp [matchAtom] at h
  | grounded g =>
      cases conc with
      | grounded hG =>
          by_cases heq : g == hG
          · simp [matchAtom, heq] at h
            cases h
            have hgg : g = hG := by
              have hatom : ((Atom.grounded g : Atom) == (Atom.grounded hG : Atom)) = true := by
                simpa [BEq.beq, Atom.beq] using heq
              have heqAtom : (Atom.grounded g : Atom) = (Atom.grounded hG : Atom) :=
                Atom.eq_of_beq_eq_true hatom
              cases heqAtom
              rfl
            subst hgg
            exact MatchAtomRel.grounded
          · simp [matchAtom, heq] at h
      | symbol _ => simp [matchAtom] at h
      | var _ => simp [matchAtom] at h
      | expression _ => simp [matchAtom] at h
  | expression es =>
      simp [matchAtom_expression_pattern_none (σ := σ) (es := es) (conc := conc)] at h

/-- Completeness of executable `matchAtom` for `MatchAtomRel`. -/
theorem matchAtom_complete {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : MatchAtomRel σ pat conc σ') :
    matchAtom σ pat conc = some σ' := by
  cases h with
  | var_fresh hlookup =>
      simp [matchAtom, hlookup]
  | var_bound hlookup =>
      simp [matchAtom, hlookup, Atom.beq_self_eq_true]
  | symbol =>
      simp [matchAtom]
  | grounded =>
      simp [matchAtom]

/-- Exact characterization of successful `matchAtom` in the supported fragment. -/
theorem matchAtom_iff {σ : Subst} {pat conc : Atom} {σ' : Subst} :
    matchAtom σ pat conc = some σ' ↔ MatchAtomRel σ pat conc σ' := by
  constructor
  · exact matchAtom_sound
  · exact matchAtom_complete

section Canaries

#check @MatchAtomRel
#check @matchAtom_sound
#check @matchAtom_complete
#check @matchAtom_iff
#check @matchAtom_expression_pattern_none

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
