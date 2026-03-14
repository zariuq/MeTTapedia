import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# MORK Match Specification

Relational specification for `matchAtom` on the currently supported MORK
fragment (variables, symbols, grounded values).  This isolates the matching
semantics from implementation details and makes the supported scope explicit.

Expression-pattern matching is intentionally unsupported in `matchAtom` today.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Relational spec for atom matching. -/
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
  /-- Empty expression matches empty expression. -/
  | expr_nil {σ : Subst} :
      MatchAtomRel σ (.expression []) (.expression []) σ
  /-- Non-empty expression matches element-wise. -/
  | expr_cons {σ σ' σ'' : Subst} {p c : Atom} {ps cs : List Atom}
      (hhead : MatchAtomRel σ p c σ')
      (htail : MatchAtomRel σ' (.expression ps) (.expression cs) σ'') :
      MatchAtomRel σ (.expression (p :: ps)) (.expression (c :: cs)) σ''

/-- Soundness of executable `matchAtom` w.r.t. `MatchAtomRel`.
    Every successful `matchAtom` call corresponds to a `MatchAtomRel` derivation. -/
theorem matchAtom_sound {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    MatchAtomRel σ pat conc σ' := by
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at h
    cases hlookup : σ.lookup v with
    | none =>
        simp [hlookup] at h; cases h
        exact MatchAtomRel.var_fresh hlookup
    | some a' =>
        by_cases heq : a == a'
        · simp [hlookup, heq] at h; cases h
          have hca := Atom.eq_of_beq_eq_true (by simpa using heq)
          subst hca; exact MatchAtomRel.var_bound hlookup
        · simp [hlookup, heq] at h
  | .symbol s, .symbol t =>
    simp only [matchAtom] at h
    split at h <;> simp_all
    exact MatchAtomRel.symbol
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at h
    split at h <;> simp_all
    exact MatchAtomRel.grounded
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression ps, .expression cs =>
    simp only [matchAtom] at h
    exact matchAtomList_sound h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  matchAtomList_sound : ∀ {σ : Subst} {ps cs : List Atom} {σ' : Subst},
      matchAtom.matchAtomList σ ps cs = some σ' →
      MatchAtomRel σ (.expression ps) (.expression cs) σ'
    | σ, [], [], σ', h => by
        simp [matchAtom.matchAtomList] at h; cases h; exact MatchAtomRel.expr_nil
    | σ, p :: ps, c :: cs, σ', h => by
        simp [matchAtom.matchAtomList] at h
        cases hm : matchAtom σ p c with
        | none => simp [hm] at h
        | some σ'' =>
          simp [hm] at h
          exact MatchAtomRel.expr_cons
            (matchAtom_sound hm)
            (matchAtomList_sound h)
    | _, [], _ :: _, _, h => by simp [matchAtom.matchAtomList] at h
    | _, _ :: _, [], _, h => by simp [matchAtom.matchAtomList] at h

/-- Completeness of executable `matchAtom` for `MatchAtomRel`.
    Every `MatchAtomRel` derivation is witnessed by `matchAtom`. -/
theorem matchAtom_complete {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : MatchAtomRel σ pat conc σ') :
    matchAtom σ pat conc = some σ' := by
  induction h with
  | var_fresh hlookup =>
      simp [matchAtom, hlookup]
  | var_bound hlookup =>
      simp [matchAtom, hlookup]
  | symbol =>
      simp [matchAtom]
  | grounded =>
      simp [matchAtom]
  | expr_nil =>
      simp [matchAtom, matchAtom.matchAtomList]
  | expr_cons _ _ ih_head ih_tail =>
      simp only [matchAtom, matchAtom.matchAtomList, ih_head]
      simp only [matchAtom] at ih_tail
      exact ih_tail

/-- Exact characterization: `matchAtom σ pat conc = some σ' ↔ MatchAtomRel σ pat conc σ'`. -/
theorem matchAtom_iff {σ : Subst} {pat conc : Atom} {σ' : Subst} :
    matchAtom σ pat conc = some σ' ↔ MatchAtomRel σ pat conc σ' :=
  ⟨matchAtom_sound, matchAtom_complete⟩

section Canaries

#check @MatchAtomRel
#check @matchAtom_sound
#check @matchAtom_complete
#check @matchAtom_iff

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
