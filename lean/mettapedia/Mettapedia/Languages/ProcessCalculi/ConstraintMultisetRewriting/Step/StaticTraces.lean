import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# The run layer's static traces are traces of dependent runs

In the one-frame instance, runs with the same firings from configurations with the same solutions
and occurrences are similar (`similar_of_firings`). A swap of two statically independent firings in a
run is a swap of dependent runs (`swap_traceEquiv`), and the intermediate words of a chain of swaps are
words of runs, because statically trace-equivalent words are executable together
(`traceEquiv_executable`, `last_consistent`). Hence two runs whose words are statically trace
equivalent are trace equivalent as dependent runs (`traceEquiv_of_static`): the word-level trace theory
of the run layer is an instance of the trace theory over the interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Transport)
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv Swap)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- **Runs with the same firings** from configurations with the same solutions and occurrences are
similar. -/
theorem similar_of_firings : ∀ {C D : Configuration T O} (r : (firstOrder A label).Run C)
    (r' : (firstOrder A label).Run D), SameUpTo A C D →
      r.word.map Sigma.snd = r'.word.map Sigma.snd → (firstOrderTransport A label).Similar r r'
  | _, _, .nil _, .nil _, same, _ => Transport.similar_nil_nil.mpr ⟨⟨same⟩⟩
  | _, _, .cons f _ rest, .cons _ _ rest', same, words => by
      simp only [Interface.Step.Run.word, List.map_cons, List.cons.injEq] at words
      obtain ⟨rfl, tails⟩ := words
      exact Transport.similar_cons_cons.mpr
        ⟨⟨same⟩, rfl, similar_of_firings rest rest' (f.result_congr A label same) tails⟩
  | _, _, .nil _, .cons _ _ _, _, words => by simp [Interface.Step.Run.word] at words
  | _, _, .cons _ _ _, .nil _, _, words => by simp [Interface.Step.Run.word] at words

/-- The end of a nonempty run of the one-frame instance has consistent knowledge. -/
theorem last_consistent : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C), r.word ≠ [] →
    A.Consistent r.last.equations
  | _, .nil _, nonempty => absurd rfl nonempty
  | _, .cons _ admitted (.nil _), _ => admitted.firing.consistent
  | _, .cons _ _ (.cons g b rest), _ =>
      last_consistent (.cons g b rest) (by simp [Interface.Step.Run.word])

/-- **A static swap in a run is a swap of dependent runs.** -/
theorem swap_traceEquiv {f g : Firing T S O} (independent : StaticIndependent label f g) :
    ∀ (u v : List (Firing T S O)) {C : Configuration T O} (r r' : (firstOrder A label).Run C),
      r.word.map Sigma.snd = u ++ f :: g :: v → r'.word.map Sigma.snd = u ++ g :: f :: v →
        (firstOrderTransport A label).TraceEquiv C r r'
  | [], v, C, r, r', words, words' => by
      rcases r with _ | ⟨f₁, a, _ | ⟨g₁, b, rest⟩⟩
      · simp [Interface.Step.Run.word] at words
      · simp [Interface.Step.Run.word] at words
      rcases r' with _ | ⟨g₂, a', _ | ⟨f₂, b', rest'⟩⟩
      · simp [Interface.Step.Run.word] at words'
      · simp [Interface.Step.Run.word] at words'
      simp only [Interface.Step.Run.word, List.map_cons, List.nil_append, List.cons.injEq] at words words'
      obtain ⟨rfl, rfl, restWord⟩ := words
      obtain ⟨rfl, rfl, restWord'⟩ := words'
      exact .rel _ _ (.inl (.here a a' rfl b rfl b'
        (similar_of_firings A label rest rest' (swap_valid A label independent a b).2.2
          (restWord.trans restWord'.symm))))
  | x :: u, v, C, r, r', words, words' => by
      rcases r with _ | ⟨x₁, a, r₁⟩
      · simp [Interface.Step.Run.word] at words
      rcases r' with _ | ⟨x₂, a', r₁'⟩
      · simp [Interface.Step.Run.word] at words'
      simp only [Interface.Step.Run.word, List.map_cons, List.cons_append, List.cons.injEq] at words words'
      obtain ⟨rfl, tail⟩ := words
      obtain ⟨rfl, tail'⟩ := words'
      exact Transport.TraceEquiv.cons (swap_traceEquiv independent u v r₁ r₁' tail tail')

/-- **Static traces are traces of dependent runs**: runs whose words are statically trace
equivalent are trace equivalent runs of the one-frame instance. -/
theorem traceEquiv_of_static {w w' : List (Firing T S O)}
    (equivalent : TraceEquiv (StaticIndependent label) w w') :
    ∀ {C : Configuration T O} (r r' : (firstOrder A label).Run C),
      r.word.map Sigma.snd = w → r'.word.map Sigma.snd = w' →
        (firstOrderTransport A label).TraceEquiv C r r' := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v independent =>
          intro C r r' words words'
          exact swap_traceEquiv A label independent u v r r' words words'
  | refl w =>
      intro C r r' words words'
      exact .rel _ _ (.inr (similar_of_firings A label r r' (SameUpTo.refl A C) (words.trans words'.symm)))
  | symm _ _ _ ih =>
      intro C r r' words words'
      exact .symm _ _ (ih r' r words' words)
  | trans w₁ w₂ w₃ first _ ih₁ ih₂ =>
      intro C r r₃ words words₃
      obtain ⟨r₂, words₂⟩ : ∃ r₂ : (firstOrder A label).Run C, r₂.word.map Sigma.snd = w₂ := by
        by_cases empty : w₁ = []
        · subst empty
          have none : w₂ = [] := List.perm_nil.mp (TraceEquiv.perm first).symm
          exact ⟨.nil C, by rw [none]; rfl⟩
        · have consistent := last_consistent A label r fun noFirings => empty (by
            rw [← words, noFirings, List.map_nil])
          have executable := (executable_iff_run A label C w₁).mpr ⟨r, words, consistent⟩
          obtain ⟨r₂, words₂, -⟩ := (executable_iff_run A label C w₂).mp
            ((traceEquiv_executable A label first C).1.mp executable)
          exact ⟨r₂, words₂⟩
      exact .trans _ _ _ (ih₁ r r₂ words words₂) (ih₂ r₂ r₃ words₂ words₃)

#print axioms similar_of_firings
#print axioms last_consistent
#print axioms swap_traceEquiv
#print axioms traceEquiv_of_static

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
