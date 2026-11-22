import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Represents

/-!
# A hosted program is its rules and its rows; the hosting of a union is the union of the hostings

A source program is hosted by a **system** (`HostedSystem`): the rules of its translation, and one
row per equation, `eqn(lhs)` at private names (`equationRows`). The rule for a call that no equation
matches reads those rows by an absence check, so the rows are part of the hosted program as much as
the rules are. The start of a query (`HostedSystem.start`) is the rows, numbered `0, …, k - 1`, and the
query's alternative at `k`; it is the folder's `start` (`start_hosted`).

**The union of two hosted systems** (`HostedSystem.union`) has the union of their rules, and the rows
of the first followed by the rows of the second, renumbered past the first's, their private names
moved with them (`shiftNames`).

* `hosted_union`: **the hosted system of `P.union Q` is the union of the hosted systems of `P` and
  `Q`**: the rules are those of `translate_union`, the rows those of `equationRows_union`.
* `start_union`: so the start of a query of the union is the start of the union of the systems.

The correspondence theorems (`runs_forward`, `runs_reflected`, the arrow forms) apply to `P.union Q`
because it is a program; this theorem adds the decomposition of its hosted system into the two
parts. The rules alone do not compose: a system whose rules are those of a union and whose rows are
those of one part answers what the union never answers (`Composition.Controls.mixed_answers_g`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}

/-- **A hosted system**: rules of the step, and rows at the start frame. -/
structure HostedSystem (S : Signature) (κ : Keys S) where
  rules : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)
  rows : List (Observation S (startArity κ))

/-- **The equation rows of a program**: equation `i`'s left side at the private names of row `i`. -/
def equationRows (P : SourceLanguage.Program κ Γ star Ty) : List (Observation S (startArity κ)) :=
  P.equations.mapIdx fun i e => observe (eqnN N (instantiate (rowNames i) e.lhs))

/-- **The hosted system of a program**: its translation and its equation rows. -/
def hosted (P : SourceLanguage.Program κ Γ star Ty) : HostedSystem S κ :=
  ⟨translate N P, equationRows N P⟩

/-- **Renumbering the private names of rows**: the copy for row `i` becomes the copy for row `i + m`;
the source's names are kept. -/
def shiftNames (m : ℕ) : Assignment (startArity κ) (startArity κ)
  | .inl x => generator (startArity κ) (.inl x)
  | .inr p => generator (startArity κ) (.inr (p.1 + m, p.2))

/-- **The union of hosted systems**: the union of the rules; the rows of the first, then the rows of
the second, renumbered past the first's. -/
def HostedSystem.union (H₁ H₂ : HostedSystem S κ) : HostedSystem S κ :=
  ⟨H₁.rules ∪ H₂.rules, H₁.rows ++ H₂.rows.map (instantiateObservation (shiftNames H₁.rows.length))⟩

/-- **The start of a query in a hosted system**: no knowledge, the rows `0, …, k - 1` and the query's
alternative at `k`, for `k` rows. -/
def HostedSystem.start (H : HostedSystem S κ) (q : Comp κ Γ star Ty) : HostState S :=
  ⟨startFrame κ, [], insert H.rows.length (Finset.range H.rows.length),
    fun o => if h : o < H.rows.length then H.rows[o] else observe (encAlt N (instantiate queryNames) (.eval q) [])⟩

theorem equationRows_length (P : SourceLanguage.Program κ Γ star Ty) :
    (equationRows N P).length = P.equations.length := by
  simp [equationRows]

theorem equationRows_getElem (P : SourceLanguage.Program κ Γ star Ty) (i : ℕ)
    (h : i < (equationRows N P).length) :
    (equationRows N P)[i] =
      observe (eqnN N (instantiate (rowNames i)
        (P.equations[i]'(by rwa [equationRows_length] at h)).lhs)) := by
  simp [equationRows]

/-- **The folder's start is the start of the hosted system.** -/
theorem start_hosted (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    start N P q = (hosted N P).start N q := by
  have length : (hosted N P).rows.length = P.equations.length := equationRows_length N P
  unfold start HostedSystem.start
  congr 1
  · rw [length]
  · funext o
    unfold startLabel
    by_cases small : o < P.equations.length
    · have small' : o < (hosted N P).rows.length := by rw [length]; exact small
      rw [dif_pos small, dif_pos small']
      exact (equationRows_getElem N P o small').symm
    · have big : ¬ o < (hosted N P).rows.length := by rw [length]; exact small
      rw [dif_neg small, dif_neg big]

/-- Renumbering moves an equation row's private names. -/
theorem shift_row (m i : ℕ) (lhs : Data κ Γ star) :
    instantiateObservation (shiftNames (κ := κ) (S := S) m) (observe (eqnN N (instantiate (rowNames i) lhs))) =
      observe (eqnN N (instantiate (rowNames (i + m)) lhs)) := by
  change observe (instantiate (shiftNames m) _) = _
  rw [instantiate_eqnN, instantiate_comp]
  apply congrArg (fun ρ => observe (eqnN N (instantiate ρ lhs)))
  funext x
  exact instantiate_generator (shiftNames m) (.inr (i, x))

/-- **The rows of a union**: the rows of the first program, then those of the second, renumbered. -/
theorem equationRows_union (P Q : SourceLanguage.Program κ Γ star Ty) :
    equationRows N (P.union Q) =
      equationRows N P ++ (equationRows N Q).map (instantiateObservation (shiftNames (equationRows N P).length)) := by
  unfold equationRows
  rw [show (P.union Q).equations = P.equations ++ Q.equations from rfl, List.mapIdx_append]
  congr 1
  rw [List.length_mapIdx]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_mapIdx, List.getElem_map]
    rw [shift_row]

/-- **The hosting of a union is the union of the hostings**: the hosted system of `P.union Q` is the
union of the hosted systems of `P` and `Q`. The correspondence theorems apply to `P.union Q` because
it is a program; this theorem adds the decomposition: its rules are the union of the rules
(`translate_union`), and its rows are the rows of `P` followed by the rows of `Q` renumbered past
them. -/
theorem hosted_union (P Q : SourceLanguage.Program κ Γ star Ty) :
    hosted N (P.union Q) = (hosted N P).union (hosted N Q) := by
  unfold hosted HostedSystem.union
  rw [translate_union, equationRows_union]

/-- **The start of a query of a union is the start of the union of the hosted systems.** -/
theorem start_union (P Q : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    start N (P.union Q) q = ((hosted N P).union (hosted N Q)).start N q := by
  rw [start_hosted, hosted_union]

#print axioms start_hosted
#print axioms equationRows_union
#print axioms hosted_union
#print axioms start_union

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
