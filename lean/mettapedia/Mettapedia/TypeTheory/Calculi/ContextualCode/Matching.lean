import Mettapedia.TypeTheory.Calculi.ContextualCode.Confluence

/-!
# Matching: inspecting code with patterns

Matching is the only place where a second level of variables appears: the
holes of a pattern. A hole is filled by closed code, so the variables bound
inside the code, among them the parameters of a template, are rigid for
matching: no hole can take one of them (`hole_never_binds`). A match hands the
handler the names of the pieces it found, so the handler's own substitution is
ordinary substitution and never enters a template.

The examples follow the Prime draft's fixture `quote_head_matching.metta`.

* `(parts @(∧ (F 0) (G 0)))`, with the equation
  `(= (parts (quote (∧ $p $q))) (both @$p @$q))`, gives
  `(both @(F 0) @(G 0))` (`parts_example`).
* The head `(show (quote ((lam $x $b) $c)))` asks a hole to take the body of an
  abstraction. Under rigid matching this fires only when the body does not
  mention the bound variable (`show_constant_body`, `show_bound_body_stuck`);
  the two ways of opening the binder are in `Destructuring.lean`.

HE issue #579 asks for a quotation whose variables neither unification nor
substitution can enter. The template `(quote $x ($x))` is such a quotation
(`issue579_*`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-! ## Rigidity -/

/-- A hole is never filled by a variable bound inside the code. -/
theorem hole_never_var {m k : Nat} (σ : Fin m → Term 0) (j : Fin m) (i : Fin k) :
    (Pat.hole j : Pat m k).fill σ ≠ .var i := by
  intro h
  have := (Pat.mentions_fill σ (Pat.hole j) i).mp (by rw [h]; exact rfl)
  exact this

/-- **No hole binds a variable of the code.** If a matched code mentions a
variable bound inside it, the pattern wrote that variable itself. -/
theorem hole_never_binds {m k : Nat} {P : Pat m k} {σ : Fin m → Term 0} {M : Term k}
    (h : P.fill σ = M) {i : Fin k} (hM : Mentions M i) : P.VarIn i :=
  (Pat.mentions_fill σ P i).mp (h ▸ hM)

/-- A match that fires. -/
theorem cmatch_steps {n m k : Nat} (P : Pat m k) (σ : Fin m → Term 0) (F : Term n)
    (covers : P.Covers) {M : Term k} (h : P.fill σ = M) :
    Step (.cmatch k (.cquote k M) P F) (appsN F (fun j => .cquote 0 (σ j))) := by
  subst h
  exact .cmatch P σ F covers

/-- A match whose template has no filling of the pattern is stuck. -/
theorem cmatch_stuck {n m k : Nat} {P : Pat m k} {M : Term k} {F : Term n} (normal : Normal F)
    (noFill : ∀ σ, P.fill σ ≠ M) : Normal (.cmatch k (.cquote k M) P F) :=
  .cmatch (.cquote k M) normal (fun σ _ h => noFill σ (cquote_inj h).symm)

/-! ## HE issue #579 -/

/-- `(quote $x ($x))`: a template whose code is its own parameter. -/
def selfParam {n : Nat} : Term n := .cquote 1 (.var 0)

/-- **Substitution cannot reach the parameter**: every substitution fixes the
template. -/
theorem issue579_subst {n m : Nat} (σ : Sub n m) :
    (Term.subst σ (.cquote 1 (.var 0) : Term n)) = .cquote 1 (.var 0) := rfl

/-- `(quote $y ($y))` is the same template: the parameter's written name is
not part of the code. -/
theorem issue579_alpha : (selfParam : Term 0) = .cquote 1 (.var 0) := rfl

/-- **Matching `(quote $x ($x))` against `(quote A)` does not fire**: the
pattern asks for a template of one parameter whose code is that parameter. -/
theorem issue579_no_match {n : Nat} (F : Term n) (normal : Normal F) :
    Normal (.cmatch 1 (.cquote 0 (.sym "A")) (Pat.var 0 : Pat 0 1) F) :=
  .cmatch (.cquote 0 _) normal (fun _ _ h => by
    simp only [Term.cquote.injEq] at h
    exact absurd h.1 (by decide))

/-- The same pattern matches the α-equivalent template `(quote $y ($y))`. -/
theorem issue579_match {n : Nat} (F : Term n) :
    Step (.cmatch 1 selfParam (Pat.var 0 : Pat 0 1) F) F :=
  @Step.cmatch n 0 1 (Pat.var 0) (fun j => j.elim0) F (fun j => j.elim0)

/-- **A hole cannot take the parameter.** -/
theorem issue579_hole_stuck {n : Nat} (F : Term n) (normal : Normal F) :
    Normal (.cmatch 1 selfParam (Pat.hole 0 : Pat 1 1) F) :=
  cmatch_stuck normal (fun σ => hole_never_var σ 0 0)

/-- `(quote $x)` with a hole matches the code of any name and hands over the
name: `(let (quote $x) (quote A) $x)` gives `(quote A)`. -/
theorem issue579_hole_takes_name {n : Nat} (F : Term n) :
    Step (.cmatch 0 (.cquote 0 (.sym "A")) (Pat.hole 0 : Pat 1 0) F)
      (.app F (.cquote 0 (.sym "A"))) :=
  cmatch_steps (Pat.hole 0) (fun _ => .sym "A") F (fun j => by
    rcases j with ⟨_ | _, hj⟩
    · rfl
    · omega) rfl

/-! ## The fixture `quote_head_matching.metta` -/

/-- The head pattern `(∧ $p $q)`. -/
def conjPat : Pat 2 0 := .app (.app (.sym "∧") (.hole 0)) (.hole 1)

theorem conjPat_covers : conjPat.Covers := by
  intro j
  rcases j with ⟨_ | _ | _, hj⟩
  · exact .inl (.inr rfl)
  · exact .inr rfl
  · omega

/-- `(F 0)` and `(G 0)`. -/
def codeF : Term 0 := .app (.sym "F") (.sym "0")
def codeG : Term 0 := .app (.sym "G") (.sym "0")

/-- The handler `(both @$p @$q)`: it receives the two names. -/
def bothHandler : Term 0 := .lam (.lam (.app (.app (.sym "both") (.var 1)) (.var 0)))

/-- **`(parts @(∧ (F 0) (G 0)))` gives `(both @(F 0) @(G 0))`.** -/
theorem parts_example :
    Steps (.cmatch 0 (.cquote 0 (.app (.app (.sym "∧") codeF) codeG)) conjPat bothHandler)
      (.app (.app (.sym "both") (.cquote 0 codeF)) (.cquote 0 codeG)) := by
  have fires := cmatch_steps conjPat (fun j => Fin.cases codeF (fun _ => codeG) j) bothHandler
    conjPat_covers (M := .app (.app (.sym "∧") codeF) codeG) rfl
  exact ((Relation.ReflTransGen.single fires).tail (.appL (.beta _ _))).tail (.beta _ _)

/-- The head pattern `((lam $x $b) $c)`: the abstraction's body is a hole
under the abstraction's binder. -/
def showPat : Pat 2 0 := .app (.lam (.hole 0)) (.hole 1)

theorem showPat_covers : showPat.Covers := by
  intro j
  rcases j with ⟨_ | _ | _, hj⟩
  · exact .inl rfl
  · exact .inr rfl
  · omega

/-- The handler `(got $b $c)`. -/
def gotHandler : Term 0 := .lam (.lam (.app (.app (.sym "got") (.var 1)) (.var 0)))

/-- A body that does not mention the binder is taken: `(show @((lam $y k) 0))`
gives `(got @k @0)`. -/
theorem show_constant_body :
    Steps (.cmatch 0 (.cquote 0 (.app (.lam (.sym "k")) (.sym "0"))) showPat gotHandler)
      (.app (.app (.sym "got") (.cquote 0 (.sym "k"))) (.cquote 0 (.sym "0"))) := by
  have fires := cmatch_steps showPat (fun j => Fin.cases (.sym "k") (fun _ => .sym "0") j)
    gotHandler showPat_covers (M := .app (.lam (.sym "k")) (.sym "0")) rfl
  exact ((Relation.ReflTransGen.single fires).tail (.appL (.beta _ _))).tail (.beta _ _)

/-- **A body that mentions the binder is not taken**: `(show @((lam $y (f $y))
0))` is stuck under rigid matching. The hole would have to capture the bound
variable. -/
theorem show_bound_body_stuck :
    Normal (.cmatch 0 (.cquote 0 (.app (.lam (.app (.sym "f") (.var 0))) (.sym "0"))) showPat
      gotHandler) := by
  refine cmatch_stuck (.lam (.lam (.app (.app (.sym _) (.var _) (fun _ h => by cases h))
    (.var _) (fun _ h => by cases h)))) ?_
  intro σ h
  simp only [showPat, Pat.fill, Term.app.injEq, Term.lam.injEq] at h
  have body : (Pat.hole 0 : Pat 2 1).fill σ = .app (.sym "f") (.var 0) := h.1
  exact hole_never_binds body (i := 0) (Or.inr rfl)

end Mettapedia.TypeTheory.Calculi.ContextualCode
