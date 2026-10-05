import Mettapedia.Languages.MM0.Presentation.FreeVariablesImages

/-! # Authored subtraction of each MM0 argument's declared bindings -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freeVariablesProgram
local notation "A" => freeVariablesEquations
local notation "H" => computationalHost
local notation "R" => ComputationalSupport.encodeResult

theorem contribution_tail_computes (free : List Nat) (tail : Option (List Nat)) :
    Applies P H "mm0:free-contribution-tail" [encodeNaturals free, R tail]
      (R (tail.map (free ++ ·))) := by
  cases tail with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some rest =>
      refine free_equation (equation := A[29])
        (environment := [("free", encodeNaturals free), ("rest", encodeNaturals rest)])
        (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (.constructor (by rfl) (by rfl))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (append_reused free rest)

private theorem contributions_start (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) (result : Term)
    (next : Applies P H "mm0:free-contributions-view"
      [listView (formal.map encodeBinder), listView (freeLists.map encodeNaturals),
        encodeContext target, encodeContext full, encodeExpressions arguments] result) :
    Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists] result := by
  refine free_equation (equation := A[20])
    (environment := [("target", encodeContext target), ("full", encodeContext full),
      ("arguments", encodeExpressions arguments), ("formal", encodeContext formal),
      ("free-lists", encodeFreeLists freeLists)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil))))) next
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))

private theorem contributions_bound (target full : Context) (arguments : List Preterm)
    (sort : Nat) (formal : Context) (free : List Nat) (freeLists : List (List Nat)) (result : Term)
    (tail : Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists] result) :
    Applies P H "mm0:free-contributions-view"
      [listView ((Kernel.Binder.bound sort :: formal).map encodeBinder),
        listView ((free :: freeLists).map encodeNaturals), encodeContext target, encodeContext full,
        encodeExpressions arguments] result := by
  refine free_equation (equation := A[24])
    (environment := [("sort", natural sort), ("formal", encodeContext formal),
      ("free", encodeNaturals free), ("free-lists", encodeFreeLists freeLists),
      ("target", encodeContext target), ("full", encodeContext full), ("arguments", encodeExpressions arguments)])
    (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) tail

private theorem contribution_binding (target full : Context) (arguments : List Preterm)
    (formal : Context) (free bound : List Nat) (freeLists : List (List Nat)) (remaining : Option (List Nat))
    (tail : Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists] (R remaining)) :
    Applies P H "mm0:free-contribution-bound" [R (some bound), encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeNaturals free, encodeFreeLists freeLists]
      (R (remaining.map (subtract free bound ++ ·))) := by
  refine free_equation (equation := A[27])
    (environment := [("bound", encodeNaturals bound), ("target", encodeContext target),
      ("full", encodeContext full), ("arguments", encodeExpressions arguments), ("formal", encodeContext formal),
      ("free", encodeNaturals free), ("free-lists", encodeFreeLists freeLists)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
    (contribution_tail_computes (subtract free bound) remaining)
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (difference_reused free bound)
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) tail

private theorem contributions_regular (target full : Context) (arguments : List Preterm)
    (sort : Nat) (dependencies : Finset Nat) (formal : Context) (free : List Nat)
    (freeLists : List (List Nat)) (result : Term)
    (next : Applies P H "mm0:free-contribution-bound"
      [R (images? target full arguments (dependencies.sort (· ≤ ·))), encodeContext target, encodeContext full,
        encodeExpressions arguments, encodeContext formal, encodeNaturals free, encodeFreeLists freeLists] result) :
    Applies P H "mm0:free-contributions-view"
      [listView ((Kernel.Binder.regular sort dependencies :: formal).map encodeBinder),
        listView ((free :: freeLists).map encodeNaturals), encodeContext target, encodeContext full,
        encodeExpressions arguments] result := by
  refine free_equation (equation := A[25])
    (environment := [("sort", natural sort), ("dependencies", encodeDependencies dependencies),
      ("formal", encodeContext formal), ("free", encodeNaturals free), ("free-lists", encodeFreeLists freeLists),
      ("target", encodeContext target), ("full", encodeContext full), ("arguments", encodeExpressions arguments)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil)))) (images_computes target full arguments _)

theorem contributions_computes (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) :
    Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists]
      (R (contributions? target full arguments formal freeLists)) := by
  induction formal generalizing freeLists with
  | nil =>
      apply contributions_start
      cases freeLists <;> exact ⟨2, by rw [free_apply _ (by decide)]; rfl⟩
  | cons binder formal ih =>
      apply contributions_start
      cases freeLists with
      | nil => cases binder <;> exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | cons free freeLists =>
          cases binder with
          | bound sort => exact contributions_bound target full arguments sort formal free freeLists _ (ih freeLists)
          | regular sort dependencies =>
              apply contributions_regular
              cases imageKnown : images? target full arguments (dependencies.sort (· ≤ ·)) with
              | none =>
                  simp only [contributions?, imageKnown, ComputationalSupport.encodeResult]
                  exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
              | some bound =>
                  cases remaining : contributions? target full arguments formal freeLists <;>
                    simpa [contributions?, imageKnown, remaining] using
                      contribution_binding target full arguments formal free bound freeLists _ (ih freeLists)

theorem contributions_result_exact (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) (result : Term) :
    Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists] result ↔
      result = R (contributions? target full arguments formal freeLists) := by
  constructor
  · exact fun run => run.deterministic (contributions_computes target full arguments formal freeLists)
  · rintro rfl; exact contributions_computes target full arguments formal freeLists

theorem contributions_accepts_iff (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) (result : Finset Nat) :
    (∃ free, Applies P H "mm0:free-contributions" [encodeContext target, encodeContext full,
      encodeExpressions arguments, encodeContext formal, encodeFreeLists freeLists] (R (some free)) ∧
      free.toFinset = result) ↔
      FreeVariables.Contributions target full arguments formal (freeLists.map List.toFinset) result := by
  rw [← FreeVariables.contributions_eq_some_iff, ← contributions_meaning]
  constructor
  · rintro ⟨free, run, rfl⟩
    have computed := (ComputationalSupport.encodeResult_injective
      ((contributions_result_exact _ _ _ _ _ _).mp run)).symm
    rw [computed]; rfl
  · intro known
    cases computed : contributions? target full arguments formal freeLists with
    | none => simp [computed] at known
    | some free =>
        refine ⟨free, ?_, ?_⟩
        · simpa only [computed] using contributions_computes target full arguments formal freeLists
        · simpa only [computed, Option.map_some, Option.some.injEq] using known

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables
