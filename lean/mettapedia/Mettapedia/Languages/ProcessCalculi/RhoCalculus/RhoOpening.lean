import Mettapedia.OSLF.MeTTaIL.Substitution

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

mutual
  /-- ρ-specific binder opening for bound names.

  Literal quoted process bodies are opaque to outer COMM-bound-name opening. -/
  def rhoOpenNameBVar (k : Nat) (u : Pattern) : Pattern → Pattern
    | .bvar n => if n == k then u else .bvar n
    | .fvar x => .fvar x
    | .apply "NQuote" [p] => .apply "NQuote" [p]
    | .apply c args => .apply c (rhoOpenNameBVarList k u args)
    | .lambda nm body => .lambda nm (rhoOpenNameBVar (k + 1) u body)
    | .multiLambda n nms body => .multiLambda n nms (rhoOpenNameBVar (k + n) u body)
    | .subst body repl => .subst (rhoOpenNameBVar (k + 1) u body) (rhoOpenNameBVar k u repl)
    | .collection ct elems rest =>
        .collection ct (rhoOpenNameBVarList k u elems) rest

  /-- List recursion for `rhoOpenNameBVar`. -/
  def rhoOpenNameBVarList (k : Nat) (u : Pattern) : List Pattern → List Pattern
    | [] => []
    | p :: ps => rhoOpenNameBVar k u p :: rhoOpenNameBVarList k u ps
end

mutual
  /-- Syntactic strict-core shape for names that may appear in rho name slots. -/
  def rhoNameCoreShape : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply "NQuote" [p] => rhoProcCoreShape p
    | _ => false

  /-- Syntactic strict-core shape for rho process bodies. -/
  def rhoProcCoreShape : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply "PZero" [] => true
    | .apply "PDrop" [n] => rhoNameCoreShape n
    | .apply "POutput" [n, q] => rhoNameCoreShape n && rhoProcCoreShape q
    | .apply "PInput" [n, .lambda none body] => rhoNameCoreShape n && rhoProcCoreShape body
    | .collection .hashBag elems none => rhoProcCoreShapeList elems
    | _ => false

  /-- List recursion for `rhoProcCoreShape`. -/
  def rhoProcCoreShapeList : List Pattern → Bool
    | [] => true
    | p :: ps => rhoProcCoreShape p && rhoProcCoreShapeList ps
end

mutual
  /-- `noBVar k p` means the bound variable `BVar k` does not occur free in `p`. -/
  def noBVar (k : Nat) : Pattern → Bool
    | .bvar n => n != k
    | .fvar _ => true
    | .apply _ args => noBVarList k args
    | .lambda _ body => noBVar (k + 1) body
    | .multiLambda n _ body => noBVar (k + n) body
    | .subst body repl => noBVar (k + 1) body && noBVar k repl
    | .collection _ elems _ => noBVarList k elems

  /-- List recursion for `noBVar`. -/
  def noBVarList (k : Nat) : List Pattern → Bool
    | [] => true
    | p :: ps => noBVar k p && noBVarList k ps
end

mutual
  /-- `noBoundUnderQuote k p` means `BVar k` never appears under a literal quote in `p`. -/
  def noBoundUnderQuote (k : Nat) : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply "NQuote" [p] => noBVar k p
    | .apply _ args => noBoundUnderQuoteList k args
    | .lambda _ body => noBoundUnderQuote (k + 1) body
    | .multiLambda n _ body => noBoundUnderQuote (k + n) body
    | .subst body repl => noBoundUnderQuote (k + 1) body && noBoundUnderQuote k repl
    | .collection _ elems _ => noBoundUnderQuoteList k elems

  /-- List recursion for `noBoundUnderQuote`. -/
  def noBoundUnderQuoteList (k : Nat) : List Pattern → Bool
    | [] => true
    | p :: ps => noBoundUnderQuote k p && noBoundUnderQuoteList k ps
end

/-- Checkable strict-core COMM-body fragment: rho-core syntax together with
    opacity hygiene for the outer COMM binder. -/
def strictCoreCommBody (p : Pattern) : Bool :=
  rhoProcCoreShape p && noBoundUnderQuote 0 p

theorem strictCoreCommBody_eq_true_iff (p : Pattern) :
    strictCoreCommBody p = true ↔
      rhoProcCoreShape p = true ∧ noBoundUnderQuote 0 p = true := by
  simp [strictCoreCommBody, Bool.and_eq_true]

/-- Negative library witness: opacity hygiene alone does not force a term to
    stay inside the strict-core rho syntax. The channel position below carries
    a process where a name would be required. -/
def strictCoreCommBodyBoundaryCounterexample : Pattern :=
  .apply "POutput"
    [.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []],
     .apply "PZero" []]

theorem strictCoreCommBodyBoundaryCounterexample_noBoundUnderQuote :
    noBoundUnderQuote 0 strictCoreCommBodyBoundaryCounterexample = true := by
  native_decide

theorem strictCoreCommBodyBoundaryCounterexample_rhoProcCoreShape_false :
    rhoProcCoreShape strictCoreCommBodyBoundaryCounterexample = false := by
  native_decide

theorem noBoundUnderQuote_not_sufficient_for_rhoProcCoreShape :
    ∃ p, noBoundUnderQuote 0 p = true ∧ rhoProcCoreShape p = false := by
  exact ⟨strictCoreCommBodyBoundaryCounterexample,
    strictCoreCommBodyBoundaryCounterexample_noBoundUnderQuote,
    strictCoreCommBodyBoundaryCounterexample_rhoProcCoreShape_false⟩

theorem noBoundUnderQuote_not_sufficient_for_strictCoreCommBody :
    ∃ p, noBoundUnderQuote 0 p = true ∧ strictCoreCommBody p = false := by
  refine ⟨strictCoreCommBodyBoundaryCounterexample,
    strictCoreCommBodyBoundaryCounterexample_noBoundUnderQuote, ?_⟩
  simp [strictCoreCommBody,
    strictCoreCommBodyBoundaryCounterexample_rhoProcCoreShape_false]

mutual
  /-- If `BVar k` does not occur in `p`, opening at `k` leaves `p` unchanged. -/
  theorem openBVar_eq_self_of_noBVar {u : Pattern} :
      ∀ {k : Nat} {p : Pattern}, noBVar k p = true → openBVar k u p = p
    | k, .bvar n, h => by
        have hnk : (n == k) = false := by
          by_cases hEq : n = k
          · subst hEq
            simp [noBVar] at h
          · exact beq_eq_false_iff_ne.mpr hEq
        simp [openBVar, hnk]
    | _, .fvar x, _ => by
        simp [openBVar]
    | k, .apply c args, h => by
        simp only [noBVar] at h
        simp [openBVar, openBVarList_eq_self_of_noBVarList (k := k) (ps := args) h]
    | k, .lambda nm body, h => by
        simp only [noBVar] at h
        simp [openBVar, openBVar_eq_self_of_noBVar (k := k + 1) (p := body) h]
    | k, .multiLambda n nms body, h => by
        simp only [noBVar] at h
        simp [openBVar, openBVar_eq_self_of_noBVar (k := k + n) (p := body) h]
    | k, .subst body repl, h => by
        simp only [noBVar, Bool.and_eq_true] at h
        simp [openBVar,
          openBVar_eq_self_of_noBVar (k := k + 1) (p := body) h.1,
          openBVar_eq_self_of_noBVar (k := k) (p := repl) h.2]
    | k, .collection ct elems rest, h => by
        simp only [noBVar] at h
        simp [openBVar, openBVarList_eq_self_of_noBVarList (k := k) (ps := elems) h]

  /-- List form of `openBVar_eq_self_of_noBVar`. -/
  theorem openBVarList_eq_self_of_noBVarList {u : Pattern} :
      ∀ {k : Nat} {ps : List Pattern}, noBVarList k ps = true → (ps.map (openBVar k u)) = ps
    | _, [], _ => by
        rfl
    | k, p :: ps, h => by
        simp only [noBVarList, Bool.and_eq_true] at h
        simp [openBVar_eq_self_of_noBVar (k := k) (p := p) h.1,
          openBVarList_eq_self_of_noBVarList (k := k) (ps := ps) h.2]
end

mutual
  /-- On the fragment with no outer bound name under literal quote, rho opening
  and generic locally nameless opening coincide. -/
  theorem rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote {u : Pattern} :
      ∀ {k : Nat} {p : Pattern},
        noBoundUnderQuote k p = true →
        rhoOpenNameBVar k u p = openBVar k u p
    | _, .bvar n, _ => by
        simp [rhoOpenNameBVar, openBVar]
    | _, .fvar x, _ => by
        simp [rhoOpenNameBVar, openBVar]
    | k, .apply "NQuote" [], h => by
        simp [rhoOpenNameBVar, rhoOpenNameBVarList, openBVar]
    | k, .apply "NQuote" [p], h => by
        simp only [noBoundUnderQuote] at h
        simp [rhoOpenNameBVar, openBVar,
          openBVar_eq_self_of_noBVar (k := k) (p := p) h]
    | k, .apply "NQuote" (p :: q :: ps), h => by
        simp only [noBoundUnderQuote, noBoundUnderQuoteList] at h
        simp [rhoOpenNameBVar, openBVar,
          rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList
            (k := k) (ps := p :: q :: ps) h]
    | k, .apply c args, h => by
        by_cases hQuote : c = "NQuote"
        · subst hQuote
          cases args with
          | nil =>
              simp [rhoOpenNameBVar, rhoOpenNameBVarList, openBVar]
          | cons a as =>
              cases as with
              | nil =>
                  simp only [noBoundUnderQuote] at h
                  simp [rhoOpenNameBVar, openBVar,
                    openBVar_eq_self_of_noBVar (k := k) (p := a) h]
              | cons b bs =>
                  simp only [noBoundUnderQuote, noBoundUnderQuoteList] at h
                  simp [rhoOpenNameBVar, openBVar,
                    rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList
                      (k := k) (ps := a :: b :: bs) h]
        · have hlist : noBoundUnderQuoteList k args = true := by
              simpa [noBoundUnderQuote, hQuote] using h
          simp [rhoOpenNameBVar, openBVar, hQuote,
            rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList (k := k) (ps := args) hlist]
    | k, .lambda nm body, h => by
        simp only [noBoundUnderQuote] at h
        simp [rhoOpenNameBVar, openBVar,
          rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote (k := k + 1) (p := body) h]
    | k, .multiLambda n nms body, h => by
        simp only [noBoundUnderQuote] at h
        simp [rhoOpenNameBVar, openBVar,
          rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote (k := k + n) (p := body) h]
    | k, .subst body repl, h => by
        simp only [noBoundUnderQuote, Bool.and_eq_true] at h
        simp [rhoOpenNameBVar, openBVar,
          rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote (k := k + 1) (p := body) h.1,
          rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote (k := k) (p := repl) h.2]
    | k, .collection ct elems rest, h => by
        simp only [noBoundUnderQuote] at h
        simp [rhoOpenNameBVar, openBVar,
          rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList (k := k) (ps := elems) h]

  /-- List form of `rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote`. -/
  theorem rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList {u : Pattern} :
      ∀ {k : Nat} {ps : List Pattern},
        noBoundUnderQuoteList k ps = true →
        rhoOpenNameBVarList k u ps = ps.map (openBVar k u)
    | _, [], _ => by
        rfl
    | k, p :: ps, h => by
        simp only [noBoundUnderQuoteList, Bool.and_eq_true] at h
        rw [rhoOpenNameBVarList, List.map_cons]
        simp [rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote (k := k) (p := p) h.1,
          rhoOpenNameBVarList_eq_openBVarList_of_noBoundUnderQuoteList (k := k) (ps := ps) h.2]
end

/-- A quoted process body is always opaque to rho opening. -/
theorem rhoOpenNameBVar_quote_opaque (k : Nat) (u p : Pattern) :
    rhoOpenNameBVar k u (.apply "NQuote" [p]) = .apply "NQuote" [p] := by
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
