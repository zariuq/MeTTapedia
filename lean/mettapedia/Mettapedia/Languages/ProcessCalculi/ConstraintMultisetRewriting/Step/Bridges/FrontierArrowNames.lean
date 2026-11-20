import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeCoreEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# The finite arrow catalogue and named source moves

The catalogue contains the six existing concrete control rules and one name
per equation ordinal. Named moves index the existing source move's children,
including a bind child whose equations have no solution. Eligibility and live
filtering are deliberately separate from this indexing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}

inductive Name where
  | ret | unmatched | left | right | eqn (index : Nat) | bindStart | bindValue
  deriving DecidableEq

variable (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)

def lookup : Name → Option (CRule S)
  | .ret => some (retRule N)
  | .unmatched => some (unmatchedRule N)
  | .left => some (choiceLeftRule N)
  | .right => some (choiceRightRule N)
  | .eqn i => (P.equations[i]?).map (schema N)
  | .bindStart => some (bindStartRule N)
  | .bindValue => some (bindValueRule N)

def names : Finset Name :=
  { .ret, .unmatched, .left, .right, .bindStart, .bindValue } ∪
    (Finset.range P.equations.length).image Name.eqn

def catalogue : FrontierNativeCore.Catalogue (translate N P) Name where
  lookup := lookup N P
  support := names P
  bounded := by
    intro name rule found
    cases name with
    | eqn index =>
        obtain ⟨equation, selected, _⟩ := Option.map_eq_some_iff.mp found
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨index, Finset.mem_range.mpr (FrontierNames.lookup_bound selected), rfl⟩)
    | _ => simp [names]
  member := by
    intro name rule found
    cases name with
    | ret => cases found; exact retRule_mem N P
    | unmatched => cases found; exact unmatchedRule_mem N P
    | left => cases found; exact choiceLeftRule_mem N P
    | right => cases found; exact choiceRightRule_mem N P
    | bindStart => cases found; exact bindStartRule_mem N P
    | bindValue => cases found; exact bindValueRule_mem N P
    | eqn index =>
        obtain ⟨equation, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        exact schema_mem N P (List.mem_of_getElem? selected)

abbrev Leaf := FrontierNativeCore.Leaf
abbrev State := FrontierNativeCore.State
abbrev Invocation := FrontierNativeCore.Invocation (catalogue N P)
abbrev Expansion := FrontierNativeCore.Expansion (catalogue N P)
abbrev Enabled := FrontierNativeCore.Enabled (catalogue N P)
abbrev Fires := FrontierNativeCore.Fires (catalogue N P)
abbrev Step := FrontierNativeCore.Step (catalogue N P)
  (fun leaf => StateFinished N leaf.state leaf.active)
abbrev target := FrontierNativeCore.theory (catalogue N P)
  (fun leaf => StateFinished N leaf.state leaf.active)

variable {N P} {supply : Nat → Term S Γ star}

variable (P) in
inductive NamedMove (w : World κ Γ star) :
    Branch κ Γ star D.Ty → Name → World κ Γ star → Branch κ Γ star D.Ty → Prop
  | ret (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps) :
      NamedMove w ⟨K, .eval (.ret t), fs, ps⟩ .ret w ⟨K, .value t, fs, ps⟩
  | unmatched (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps)
      (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) :
      NamedMove w ⟨K, .eval (.apply t), fs, ps⟩ .unmatched w ⟨K, .value t, fs, ps⟩
  | left (K : List (Constraint κ Γ star)) (c d : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .eval (.choice c d), fs, ps⟩ .left w ⟨K, .eval c, fs, ps⟩
  | right (K : List (Constraint κ Γ star)) (c d : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .eval (.choice c d), fs, ps⟩ .right w ⟨K, .eval d, fs, ps⟩
  | eqn (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps) (i : ℕ)
      (e : SourceLanguage.Equation κ Γ star D.Ty) (get : P.equations[i]? = some e)
      (matched : ∃ e' ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e'.lhs, t)])) :
      NamedMove w ⟨K, .eval (.apply t), fs, ps⟩ (.eqn i) w.fresh (callBranch D w.scope K t fs ps e)

  | letStart (K : List (Constraint κ Γ star)) (s : κ.Site) (p : Data κ Γ star)
      (c k : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .eval (.let_ s p c k), fs, ps⟩ .bindStart w
        ⟨K, .eval c, .bindTo s p k :: fs, ps⟩
  | letBind (K : List (Constraint κ Γ star)) (v : Data κ Γ star) (s : κ.Site)
      (p : Data κ Γ star) (k : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .value v, .bindTo s p k :: fs, ps⟩ .bindValue w.fresh
        ⟨K ++ [(instantiate (openAt κ s w.scope) p, v)], .eval (k.inst (openAt κ s w.scope)), fs, ps⟩

/-- **A name selects one child**: two named moves of one alternative by one name agree. -/
theorem NamedMove.unique {w w₁ w₂ : World κ Γ star} {b b₁ b₂ : Branch κ Γ star D.Ty} {n : Name}
    (first : NamedMove P w b n w₁ b₁) (second : NamedMove P w b n w₂ b₂) : w₁ = w₂ ∧ b₁ = b₂ := by
  cases first with
  | ret => cases second; exact ⟨rfl, rfl⟩
  | unmatched => cases second; exact ⟨rfl, rfl⟩
  | left => cases second; exact ⟨rfl, rfl⟩
  | right => cases second; exact ⟨rfl, rfl⟩
  | eqn K t fs ps i e get matched =>
      cases second with
      | eqn _ _ _ _ _ e' get' _ =>
          rw [get] at get'
          cases get'
          exact ⟨rfl, rfl⟩

  | letStart => cases second; exact ⟨rfl, rfl⟩
  | letBind => cases second; exact ⟨rfl, rfl⟩


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
