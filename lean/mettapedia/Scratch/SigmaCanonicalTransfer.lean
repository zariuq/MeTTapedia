/-
σ-canonical transfer: if a substitution σ (e.g. the elimination-trace
substitution of a successful whole-binding reconciliation) identifies two
atoms, then a canonical valuation χ (e.g. LeaTTa's class resolver
`leaClassSolution out`) also identifies them, given two interface facts:
variable-to-variable σ-steps are χ-identified (recorded aliases +
class-constancy), and variables with non-variable σ-images unfold to
non-variable class picks with matching σ-images.

This is the generic alias-coherence engine for the reconciliation
resolver-satisfaction obligation: both `χ key = χ-image value` for value
entries and the two-value class-coherence goal are direct instances.
-/
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

private theorem sigmaTransfer_size_pos (a : Metta.Atom) : 0 < a.size := by
  cases a <;> simp only [Metta.Atom.size] <;> omega

private theorem sigmaTransfer_size_lt_of_mem {a : Metta.Atom} :
    ∀ {l : List Metta.Atom}, a ∈ l → a.size < (Metta.Atom.expr l).size
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
      omega
    | inr h2 =>
      have ih := sigmaTransfer_size_lt_of_mem h2
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at ih ⊢
      omega

private theorem sigmaTransfer_map
    (σ χ : String → Metta.Atom) :
    ∀ (xs ys : List Metta.Atom),
      (∀ z ∈ xs, ∀ w, applyClassSolution σ z = applyClassSolution σ w →
        applyClassSolution χ z = applyClassSolution χ w) →
      xs.map (applyClassSolution σ) = ys.map (applyClassSolution σ) →
      xs.map (applyClassSolution χ) = ys.map (applyClassSolution χ)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, htr, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨htr x List.mem_cons_self y h.1,
      sigmaTransfer_map σ χ xs ys
        (fun z hz => htr z (List.mem_cons_of_mem x hz)) h.2⟩

/-- **σ-canonical transfer.**  If `σ` identifies two atoms, so does `χ`,
provided: (`hvv`) whenever `σ` sends a variable to a variable, `χ`
identifies the two variables (in the intended instantiation, variable–
variable σ-steps are recorded reconciliation aliases and the class resolver
is class-constant); and (`hpick`) whenever `σ` sends a variable `p` to a
non-variable, there is a non-variable pick `v` — the class value the
resolver unfolds through — with the same σ-image as `p` and with
`χ p` equal to the `χ`-image of `v`. -/
theorem sigma_canonical_transfer
    (σ χ : String → Metta.Atom)
    (hvv : ∀ p r, σ p = .var r → χ p = χ r)
    (hpick : ∀ p, (∀ r, σ p ≠ .var r) →
      ∃ v, (∀ r, v ≠ Metta.Atom.var r) ∧
        applyClassSolution σ v = σ p ∧
        χ p = applyClassSolution χ v) :
    ∀ a b, applyClassSolution σ a = applyClassSolution σ b →
      applyClassSolution χ a = applyClassSolution χ b := by
  suffices key : ∀ n a b, (applyClassSolution σ a).size ≤ n →
      applyClassSolution σ a = applyClassSolution σ b →
      applyClassSolution χ a = applyClassSolution χ b by
    exact fun a b hab => key (applyClassSolution σ a).size a b le_rfl hab
  intro n
  induction n with
  | zero =>
    intro a b hsize _
    exact absurd hsize (by
      have := sigmaTransfer_size_pos (applyClassSolution σ a)
      omega)
  | succ n ihn =>
    intro a b hsize hab
    have nn : ∀ x y, (∀ r, x ≠ Metta.Atom.var r) → (∀ r, y ≠ Metta.Atom.var r) →
        (applyClassSolution σ x).size ≤ n + 1 →
        applyClassSolution σ x = applyClassSolution σ y →
        applyClassSolution χ x = applyClassSolution χ y := by
      intro x y hx hy hxsize hxy
      cases x with
      | var r => exact absurd rfl (hx r)
      | sym s =>
        cases y with
        | var r => exact absurd rfl (hy r)
        | sym t =>
          simp only [applyClassSolution] at hxy ⊢
          exact hxy
        | gnd g =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
        | expr ys =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
      | gnd g =>
        cases y with
        | var r => exact absurd rfl (hy r)
        | sym t =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
        | gnd g' =>
          simp only [applyClassSolution] at hxy ⊢
          exact hxy
        | expr ys =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
      | expr xs =>
        cases y with
        | var r => exact absurd rfl (hy r)
        | sym t =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
        | gnd g =>
          simp only [applyClassSolution] at hxy
          exact Metta.Atom.noConfusion hxy
        | expr ys =>
          simp only [applyClassSolution, Metta.Atom.expr.injEq] at hxy ⊢
          refine sigmaTransfer_map σ χ xs ys ?_ hxy
          intro z hz w hzw
          have hmem : applyClassSolution σ z ∈ List.map (applyClassSolution σ) xs :=
            List.mem_map.mpr ⟨z, hz, rfl⟩
          have hlt := sigmaTransfer_size_lt_of_mem hmem
          have hexp : (Metta.Atom.expr (List.map (applyClassSolution σ) xs)).size ≤ n + 1 := by
            simpa only [applyClassSolution] using hxsize
          exact ihn z w (by omega) hzw
    have reduce : ∀ c, (∀ r, applyClassSolution σ c ≠ .var r) →
        ∃ c', (∀ r, c' ≠ Metta.Atom.var r) ∧
          applyClassSolution σ c' = applyClassSolution σ c ∧
          applyClassSolution χ c' = applyClassSolution χ c := by
      intro c hc
      cases c with
      | var p =>
        have hp : ∀ r, σ p ≠ .var r := by
          intro r h
          exact hc r (by simpa only [applyClassSolution] using h)
        obtain ⟨v, h1, h2, h3⟩ := hpick p hp
        refine ⟨v, h1, ?_, ?_⟩
        · simpa only [applyClassSolution] using h2
        · simpa only [applyClassSolution] using h3.symm
      | sym s => exact ⟨.sym s, fun r h => Metta.Atom.noConfusion h, rfl, rfl⟩
      | gnd g => exact ⟨.gnd g, fun r h => Metta.Atom.noConfusion h, rfl, rfl⟩
      | expr xs => exact ⟨.expr xs, fun r h => Metta.Atom.noConfusion h, rfl, rfl⟩
    by_cases hvar : ∃ r, applyClassSolution σ a = .var r
    · obtain ⟨r, hr⟩ := hvar
      cases a with
      | var p =>
        have hp : σ p = .var r := by simpa only [applyClassSolution] using hr
        cases b with
        | var q =>
          have hq : σ q = .var r := by
            have hb : applyClassSolution σ (.var q) = .var r := by
              rw [← hab]; exact hr
            simpa only [applyClassSolution] using hb
          have hpq := (hvv p r hp).trans (hvv q r hq).symm
          simpa only [applyClassSolution] using hpq
        | sym s =>
          rw [hab] at hr
          simp only [applyClassSolution] at hr
          exact Metta.Atom.noConfusion hr
        | gnd g =>
          rw [hab] at hr
          simp only [applyClassSolution] at hr
          exact Metta.Atom.noConfusion hr
        | expr ys =>
          rw [hab] at hr
          simp only [applyClassSolution] at hr
          exact Metta.Atom.noConfusion hr
      | sym s =>
        simp only [applyClassSolution] at hr
        exact Metta.Atom.noConfusion hr
      | gnd g =>
        simp only [applyClassSolution] at hr
        exact Metta.Atom.noConfusion hr
      | expr xs =>
        simp only [applyClassSolution] at hr
        exact Metta.Atom.noConfusion hr
    · have hvar' : ∀ r, applyClassSolution σ a ≠ .var r := fun r h => hvar ⟨r, h⟩
      have hbvar : ∀ r, applyClassSolution σ b ≠ .var r := by
        intro r h
        exact hvar' r (by rw [hab]; exact h)
      obtain ⟨a', ha1, ha2, ha3⟩ := reduce a hvar'
      obtain ⟨b', hb1, hb2, hb3⟩ := reduce b hbvar
      have hmain : applyClassSolution χ a' = applyClassSolution χ b' := by
        refine nn a' b' ha1 hb1 ?_ ?_
        · rw [ha2]; exact hsize
        · rw [ha2, hb2]; exact hab
      rw [← ha3, ← hb3]
      exact hmain

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
