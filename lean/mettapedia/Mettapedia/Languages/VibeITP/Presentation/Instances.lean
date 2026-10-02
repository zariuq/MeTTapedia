import Mettapedia.Languages.VibeITP.Presentation.Decode

/-!
# Vibe-ITP presentation: computing rule instances

Substitution of an argument vector into a first-order schema, computed by
rewriting.  Data patterns have no metavariables and are fixed by every
substitution; this covers the numeral and symbol constants that occur in rule
schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.VibeITP.Spec

theorem ab_fvar_hit (x : String) (v : Pattern) (σ : Bindings) :
    applyBindings ((x, v) :: σ) (.fvar x) = v := by
  simp [applyBindings]

theorem ab_fvar_miss (x y : String) (v : Pattern) (σ : Bindings) (h : x ≠ y) :
    applyBindings ((x, v) :: σ) (.fvar y) = applyBindings σ (.fvar y) := by
  have hb : (x == y) = false := by simp [h]
  simp [applyBindings, List.find?, hb]

theorem ab_apply (σ : Bindings) (c : String) (args : List Pattern) :
    applyBindings σ (.apply c args) = .apply c (args.map (applyBindings σ)) := by
  simp [applyBindings]

theorem ab_data (σ : Bindings) : ∀ {p : Pattern}, IsData p → applyBindings σ p = p
  | .apply c args, .apply _ _ h => by
      rw [ab_apply]
      congr 1
      conv_rhs => rw [← List.map_id args]
      apply List.map_congr_left
      intro a ha
      exact ab_data σ (h a ha)

/-! ## Constants are data -/

theorem isData_encUnary : ∀ n : Nat, IsData (encUnary n)
  | 0 => IsData.app0 _
  | n + 1 => IsData.app1 _ (isData_encUnary n)

theorem isData_encKind (k : SymKind) : IsData (encKind k) := by
  cases k <;> exact IsData.app0 _

theorem isData_encSym (sig : Sig) (s : SymId) : IsData (encSym sig s) := by
  unfold encSym
  split
  · exact IsData.app3 _ (isData_encNat _) (isData_encKind _) (isData_encNatList _)
  · exact IsData.app3 _ (isData_encNat _) (IsData.app0 _) (IsData.app0 _)

mutual
theorem isData_encTerm (sig : Sig) : ∀ t : Term, IsData (encTerm sig t)
  | .bvar i => by simp only [encTerm]; exact IsData.app1 _ (isData_encNat i)
  | .lit bytes => by simp only [encTerm]; exact IsData.app1 _ (isData_encBytes bytes)
  | .app s args => by
      simp only [encTerm]
      exact IsData.app3 _ (isData_encSym sig s) (isData_encTermList sig args)
        (IsData.app2 _ (isData_encNat _) (isData_encBool _))
theorem isData_encTermList (sig : Sig) : ∀ ts : List Term, IsData (encTermList sig ts)
  | [] => by simp only [encTermList]; exact IsData.app0 _
  | t :: ts => by
      simp only [encTermList]
      exact IsData.app2 _ (isData_encTerm sig t) (isData_encTermList sig ts)
end

@[simp] theorem ab_patTwo64 (σ : Bindings) : applyBindings σ patTwo64 = patTwo64 :=
  ab_data σ (isData_encNat _)
@[simp] theorem ab_patMaxWord (σ : Bindings) : applyBindings σ patMaxWord = patMaxWord :=
  ab_data σ (isData_encNat _)
@[simp] theorem ab_patByteBound (σ : Bindings) : applyBindings σ patByteBound = patByteBound :=
  ab_data σ (isData_encNat _)
@[simp] theorem ab_patWordBits (σ : Bindings) : applyBindings σ patWordBits = patWordBits :=
  ab_data σ (isData_encUnary _)
@[simp] theorem ab_patOne (σ : Bindings) : applyBindings σ patOne = patOne :=
  ab_data σ (isData_encNat _)
@[simp] theorem ab_patEight (σ : Bindings) : applyBindings σ patEight = patEight :=
  ab_data σ (isData_encNat _)
@[simp] theorem ab_patBuiltinSym (σ : Bindings) (b : Builtin) :
    applyBindings σ (patBuiltinSym b) = patBuiltinSym b :=
  ab_data σ (isData_encSym _ _)

theorem isData_patTwo64 : IsData patTwo64 := isData_encNat _
theorem isData_patMaxWord : IsData patMaxWord := isData_encNat _
theorem isData_patByteBound : IsData patByteBound := isData_encNat _
theorem isData_patWordBits : IsData patWordBits := isData_encUnary _
theorem isData_patOne : IsData patOne := isData_encNat _
theorem isData_patEight : IsData patEight := isData_encNat _
theorem isData_patBuiltinSym (b : Builtin) : IsData (patBuiltinSym b) := isData_encSym _ _

/-! ## Introducing a rule instance -/

theorem FODerivable.intro {R : List FORule} {r : FORule} (hr : r ∈ R)
    (args : List Pattern) (hlen : args.length = r.vars.length)
    (hdata : ∀ a ∈ args, IsData a) {J : Pattern} (hJ : r.instConclusion args = J)
    (hprem : ∀ p ∈ r.instPremises args, FODerivable R p) : FODerivable R J := by
  subst hJ
  exact .rule r hr args hlen (fun a ha => isData_valid (hdata a ha)) hprem

end Mettapedia.Languages.VibeITP.Presentation
