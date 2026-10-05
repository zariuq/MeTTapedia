import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportTable

/-!
# The rows of the transport table hold

A value side has the transport table (`CoeTable`) when its rules contain the
root computations of the transport's constants and its roles inspect their type
arguments for head forms. Every row of the table then holds as a statement
about weak-head reduction (`CoeTable.coeRules`):

* the transport inspects the target; a target that reduces to a head form
  dispatches, and a source that reduces to a head form is read by the constant
  the target dispatched to;
* a type that reduces to no head form reduces to a term stuck on the daimon;
  the transport, which cannot inspect it, is then a type case stuck on the
  daimon (`Daimonic.typeStuck`);
* every weak-head normal form of an interpreted type is a head form or stuck on
  the daimon (`ValueSide.TypeForm.split`), so the rows cover every pair of
  interpreted types. The type constants are read from the roles, so every
  inductive type has its row, whatever inductive types the roles declare.

The table is a property of a consistency model with a daimon; its rows hold on
every value side over such a model (`CoeTable.coeRules`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Realizability

open Normalization
open Consistency (appSpine_const_ne_pi appSpine_const_ne_sigma appSpine_const_eq_const)
open UniverseLevel (LevelOrder)
open ValueSide (coeApp coeArg)

variable {Head L : Type} [LevelOrder L]

/-! ## Head forms of daimonic terms and of type forms -/

/-- Whether a daimonic term is a head form is decided: it is one exactly when it
is a spine of the daimon, when the daimon is rigid. -/
theorem Daimonic.headForm_or_not {roles : Roles Head} {star : DeclName}
    (rigid : roles star = .rigid) {n : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t) :
    HeadForm roles t ∨ ¬ HeadForm roles t := by
  induction daimonic with
  | star => exact .inl ⟨_, .spine [] fun _ _ h => by rw [rigid] at h; cases h⟩
  | @app f a df ih =>
      rcases ih with ⟨key, view⟩ | notHead
      · cases view with
        | @spine c args notComputing =>
            refine .inl ⟨.const c, ?_⟩
            rw [← appSpine_concat]
            exact .spine _ notComputing
        | head h => exact absurd rfl df.ne_head
        | pi A B => exact absurd rfl df.ne_pi
        | sigma A B => exact absurd rfl df.ne_sigma
        | id A x y => exact absurd rfl df.ne_id
        | lam body => exact absurd rfl ((df.neutral rigid).ne_lam)
        | pair x y => exact absurd rfl ((df.neutral rigid).ne_pair)
        | refl x => exact absurd rfl ((df.neutral rigid).ne_refl)
      · refine .inr fun ⟨key, view⟩ => ?_
        generalize e : Tm.app f a = t at view
        cases view with
        | @spine c args notComputing =>
            obtain ⟨init, -, hf⟩ := appSpine_const_eq_app e.symm
            exact notHead ⟨.const c, hf ▸ .spine init notComputing⟩
        | _ => cases e
  | fst _ _ =>
      refine .inr fun ⟨key, view⟩ => ?_
      generalize e : Tm.fst _ = t at view
      cases view with
      | spine args _ => exact appSpine_const_ne_fst e.symm
      | _ => cases e
  | snd _ _ =>
      refine .inr fun ⟨key, view⟩ => ?_
      generalize e : Tm.snd _ = t at view
      cases view with
      | spine args _ => exact appSpine_const_ne_snd e.symm
      | _ => cases e
  | stuck role _ _ _ =>
      exact .inr fun ⟨key, view⟩ => headView_constSpine_stuck view _ _ role
  | typeStuck role _ _ _ _ _ =>
      exact .inr fun ⟨key, view⟩ => headView_constSpine_stuck view _ _ role

end Realizability

namespace ValueSide

open Normalization
open Consistency (appSpine_const_ne_pi appSpine_const_ne_sigma appSpine_const_eq_const)
open UniverseLevel (LevelOrder)
open Realizability

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

section Forms

variable (laws : V.Laws)
include laws

/-- A type constant does not compute. -/
theorem TypeConst.stuck {c : DeclName} (hc : TypeConst V c) :
    ∀ arity inspect, V.roles c ≠ .computes arity inspect := by
  rcases hc with rfl | ⟨cs, role⟩
  · intro _ _ h
    rw [laws.values.prop] at h
    cases h
  · intro _ _ h
    rw [role] at h
    cases h

/-- A form at which the transport returns its method is a head form. -/
theorem MethodForm.headForm {n : Nat} {w : Tm Head n} (form : MethodForm V w) :
    HeadForm V.roles w := by
  rcases form with ⟨h, rfl, -⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, role, -, -⟩
  · exact ⟨_, .head h⟩
  · exact ⟨_, .id A a b⟩
  · exact ⟨_, .spine [c] fun _ _ h => by rw [laws.values.holds] at h; cases h⟩
  · exact ⟨_, .spine args fun _ _ h => by rw [role] at h; cases h⟩

/-- **A weak-head normal form of an interpreted type is a head form, or stuck on
the daimon and no head form.** -/
theorem TypeForm.split {n : Nat} {w : Tm Head n} (form : TypeForm V w) :
    HeadForm V.roles w ∨ (Daimonic V.roles V.star w ∧ ¬ HeadForm V.roles w) := by
  rcases form with ⟨u, rfl, -⟩ | ⟨c, hc, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | method | daimonic
  · exact .inl ⟨_, .head u⟩
  · exact .inl ⟨_, .spine [] (hc.stuck laws)⟩
  · exact .inl ⟨_, .pi A B⟩
  · exact .inl ⟨_, .sigma A B⟩
  · exact .inl (method.headForm laws)
  · rcases daimonic.headForm_or_not laws.star with hw | hw
    · exact .inl hw
    · exact .inr ⟨daimonic, hw⟩

/-- At a form at which the transport returns its method, its row is the
method. -/
theorem MethodForm.coeTarget (N : CoeNames) {n : Nat} {X w d : Tm Head n}
    (form : MethodForm V w) : CoeTarget (coeParamsOf V.toModel V.star) N X w d d := by
  have notConst : ∀ c, (coeParamsOf V.toModel V.star).TypeConst c → w ≠ .const c :=
    fun _ hc => form.ne_typeConst hc
  rcases form with ⟨h, rfl, hh⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, role, -, -⟩
  · exact .ground hh
  · exact .method ⟨⟨_, .id A a b⟩, fun _ => nofun, fun _ _ => nofun, fun _ _ => nofun, notConst⟩
  · exact .method ⟨MethodForm.headForm laws (.inr (.inr (.inl ⟨c, rfl⟩))), fun _ => nofun,
      fun _ _ => nofun, fun _ _ => nofun, notConst⟩
  · exact .method ⟨⟨_, .spine args fun _ _ h => nomatch role.symm.trans h⟩,
      fun _ => appSpine_const_ne_head, fun _ _ => appSpine_const_ne_pi,
      fun _ _ => appSpine_const_ne_sigma, notConst⟩

/-- A daimonic head form is a form at which `coe` returns its method. -/
theorem methodTarget_of_daimonic {n : Nat} {w : Tm Head n}
    (daimonic : Daimonic V.roles V.star w) (form : HeadForm V.roles w) :
    MethodTarget (coeParamsOf V.toModel V.star) w :=
  ⟨form, fun _ => daimonic.ne_head, fun _ _ => daimonic.ne_pi, fun _ _ => daimonic.ne_sigma,
    fun c hc => by
      rcases hc with rfl | ⟨cs, role⟩
      · exact laws.daimonic_ne_prop daimonic
      · exact laws.daimonic_ne_inductive daimonic role (args := [])⟩

end Forms

end ValueSide

namespace Realizability

open Normalization
open Consistency (appSpine_const_ne_pi appSpine_const_ne_sigma appSpine_const_eq_const)
open UniverseLevel (LevelOrder)
open ValueSide (coeApp coeArg)

variable {Head L : Type} [LevelOrder L]

/-! ## The table in a value side -/

/-- **A value side with the transport table**: the roles of the transport's
constants inspect their type arguments for head forms, and the rows are root
steps of the value side. -/
structure CoeTable (M : Consistency.Model Head L) (star : DeclName) (N : CoeNames) : Prop where
  roleCoe : M.roles N.coe = .computes 3 (headAt 1)
  roleU : M.roles N.coeU = .computes 3 headAtBoth
  roleConst : M.roles N.coeConst = .computes 3 (headAt 1)
  rolePi : M.roles N.coePi = .computes 4 (headAt 2)
  roleSigma : M.roles N.coeSigma = .computes 4 (headAt 2)
  stepCoe : ∀ {n : Nat} {l r : Tm Head n}, (coeComputation (coeParamsOf M star) N).step l r →
    M.rules.computation.step l r
  stepU : ∀ {n : Nat} {l r : Tm Head n}, (coeUComputation (coeParamsOf M star) N).step l r →
    M.rules.computation.step l r
  stepConst : ∀ {n : Nat} {l r : Tm Head n},
    (coeConstComputation (coeParamsOf M star) N).step l r → M.rules.computation.step l r
  stepPi : ∀ {n : Nat} {l r : Tm Head n}, (coePiComputation (coeParamsOf M star) N).step l r →
    M.rules.computation.step l r
  stepSigma : ∀ {n : Nat} {l r : Tm Head n}, (coeSigmaComputation (coeParamsOf M star) N).step l r →
    M.rules.computation.step l r

/-- Reduction at the value a single head-form inspection reads. -/
theorem whRed_headAt {R : Rules Head} {roles : Roles Head} {c : DeclName} {arity : Nat}
    {n : Nat} {before after : List (Tm Head n)}
    (role : roles c = .computes arity (headAt before.length))
    (length : ∀ x : Tm Head n, (before ++ x :: after).length = arity) {a a' : Tm Head n}
    (red : WhRed R roles a a') :
    WhRed R roles (appSpine (.const c) (before ++ a :: after))
      (appSpine (.const c) (before ++ a' :: after)) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.scrutinee role (length _) (.here rfl) step)

namespace CoeTable

variable {M : Consistency.Model Head L} {star : DeclName} {N : CoeNames}
  (table : CoeTable M star N)
include table

/-! ### Reduction at the inspected values -/

theorem red_target {n : Nat} {X Y Y' d : Tm Head n} (red : WhRed M.rules M.roles Y Y') :
    WhRed M.rules M.roles (coeApp N.coe X Y d) (coeApp N.coe X Y' d) :=
  whRed_headAt (before := [X]) (after := [d]) table.roleCoe (fun _ => rfl) red

theorem red_univ {n : Nat} {T X X' d : Tm Head n} {key : InspectKey}
    (viewT : HeadView M.roles T key) (red : WhRed M.rules M.roles X X') :
    WhRed M.rules M.roles (appSpine (.const N.coeU) [T, X, d])
      (appSpine (.const N.coeU) [T, X', d]) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail (.scrutinee table.roleU rfl
        (.headForm (before := []) (after := [_, d]) rfl viewT
          (.here (before := [T]) (after := [d]) rfl)) step)

theorem red_const {n : Nat} {C X X' d : Tm Head n} (red : WhRed M.rules M.roles X X') :
    WhRed M.rules M.roles (appSpine (.const N.coeConst) [C, X, d])
      (appSpine (.const N.coeConst) [C, X', d]) :=
  whRed_headAt (before := [C]) (after := [d]) table.roleConst (fun _ => rfl) red

theorem red_pi {n : Nat} {A' B'' X X' f : Tm Head n} (red : WhRed M.rules M.roles X X') :
    WhRed M.rules M.roles (appSpine (.const N.coePi) [A', B'', X, f])
      (appSpine (.const N.coePi) [A', B'', X', f]) :=
  whRed_headAt (before := [A', B'']) (after := [f]) table.rolePi (fun _ => rfl) red

theorem red_sigma {n : Nat} {A' B'' X X' p : Tm Head n} (red : WhRed M.rules M.roles X X') :
    WhRed M.rules M.roles (appSpine (.const N.coeSigma) [A', B'', X, p])
      (appSpine (.const N.coeSigma) [A', B'', X', p]) :=
  whRed_headAt (before := [A', B'']) (after := [p]) table.roleSigma (fun _ => rfl) red

/-! ### Root steps -/

theorem step_coe {n : Nat} {X Y d r : Tm Head n} (h : CoeTarget (coeParamsOf M star) N X Y d r) :
    WhStep M.rules M.roles (coeApp N.coe X Y d) r :=
  .root (table.stepCoe ⟨[X, Y, d], rfl, X, Y, d, rfl, h⟩)

theorem step_univ {n : Nat} {T X d r : Tm Head n} (h : CoeUniv (coeParamsOf M star) T X d r) :
    WhStep M.rules M.roles (appSpine (.const N.coeU) [T, X, d]) r :=
  .root (table.stepU ⟨[T, X, d], rfl, T, X, d, rfl, h⟩)

theorem step_const {n : Nat} {C X d r : Tm Head n} (h : CoeConst (coeParamsOf M star) C X d r) :
    WhStep M.rules M.roles (appSpine (.const N.coeConst) [C, X, d]) r :=
  .root (table.stepConst ⟨[C, X, d], rfl, C, X, d, rfl, h⟩)

theorem step_pi {n : Nat} {A' B'' X f r : Tm Head n}
    (h : CoePiRow (coeParamsOf M star) N A' B'' X f r) :
    WhStep M.rules M.roles (appSpine (.const N.coePi) [A', B'', X, f]) r :=
  .root (table.stepPi ⟨[A', B'', X, f], rfl, A', B'', X, f, rfl, h⟩)

theorem step_sigma {n : Nat} {A' B'' X p r : Tm Head n}
    (h : CoeSigmaRow (coeParamsOf M star) N A' B'' X p r) :
    WhStep M.rules M.roles (appSpine (.const N.coeSigma) [A', B'', X, p]) r :=
  .root (table.stepSigma ⟨[A', B'', X, p], rfl, A', B'', X, p, rfl, h⟩)

/-- A β-redex at the target of a transport contracts. -/
theorem step_target_beta {n : Nat} {X d a : Tm Head n} {body : Tm Head (n + 1)} :
    WhStep M.rules M.roles (coeApp N.coe X (.app (.lam body) a) d)
      (coeApp N.coe X (inst0 a body) d) :=
  .scrutinee table.roleCoe rfl (.here (before := [X]) (after := [d]) rfl) (.beta body a)

/-! ### Transports stuck on the daimon -/

theorem daimonic_coe {n : Nat} {X w d : Tm Head n} (daimonic : Daimonic M.roles star w)
    (notHead : ¬ HeadForm M.roles w) : Daimonic M.roles star (coeApp N.coe X w d) :=
  .typeStuck table.roleCoe rfl (.here (before := [X]) (after := [d]) rfl) daimonic notHead

theorem daimonic_univ {n : Nat} {T w d : Tm Head n} {key : InspectKey}
    (viewT : HeadView M.roles T key) (daimonic : Daimonic M.roles star w)
    (notHead : ¬ HeadForm M.roles w) :
    Daimonic M.roles star (appSpine (.const N.coeU) [T, w, d]) :=
  .typeStuck table.roleU rfl
    (.headForm (before := []) (after := [w, d]) rfl viewT
      (.here (before := [T]) (after := [d]) rfl)) daimonic notHead

theorem daimonic_const {n : Nat} {C w d : Tm Head n} (daimonic : Daimonic M.roles star w)
    (notHead : ¬ HeadForm M.roles w) :
    Daimonic M.roles star (appSpine (.const N.coeConst) [C, w, d]) :=
  .typeStuck table.roleConst rfl (.here (before := [C]) (after := [d]) rfl) daimonic notHead

theorem daimonic_pi {n : Nat} {A' B'' w f : Tm Head n} (daimonic : Daimonic M.roles star w)
    (notHead : ¬ HeadForm M.roles w) :
    Daimonic M.roles star (appSpine (.const N.coePi) [A', B'', w, f]) :=
  .typeStuck table.rolePi rfl (.here (before := [A', B'']) (after := [f]) rfl) daimonic notHead

theorem daimonic_sigma {n : Nat} {A' B'' w p : Tm Head n} (daimonic : Daimonic M.roles star w)
    (notHead : ¬ HeadForm M.roles w) :
    Daimonic M.roles star (appSpine (.const N.coeSigma) [A', B'', w, p]) :=
  .typeStuck table.roleSigma rfl (.here (before := [A', B'']) (after := [p]) rfl) daimonic
    notHead

/-! ### The rows -/

omit table in
/-- **The transport table holds.** On a value side over a consistency model with
the transport table, `coe` reduces by every row of `CoeRules`, at every type
constant its roles declare. -/
theorem coeRules {V : ValueSide.Model Head L} (table : CoeTable V.toModel V.star N)
    (laws : V.Laws) : ValueSide.CoeRules V N.coe where
  univ := by
    intro n X Y d u u' rY hu rX hu' le
    exact (table.red_target rY).trans (.head (table.step_coe (.univ hu))
      ((table.red_univ (.head u) rX).tail (table.step_univ (.method hu' le))))
  univOther := by
    intro n X Y d w u rY hu rX form other
    have pre : WhRed V.rules V.roles (coeApp N.coe X Y d)
        (appSpine (.const N.coeU) [.head u, w, d]) :=
      (table.red_target rY).trans (.head (table.step_coe (.univ hu))
        (table.red_univ (.head u) rX))
    rcases ValueSide.TypeForm.split laws form with hw | ⟨dw, nw⟩
    · refine ⟨_, pre.tail (table.step_univ (.star ⟨_, .head u⟩ hw fun u₀ u₁ eT eX hu₁ => ?_)),
        .star⟩
      cases eT
      exact other u₁ eX hu₁
    · exact ⟨_, pre, table.daimonic_univ (.head u) dw nw⟩
  const := by
    intro n X Y d c hc rY rX
    exact (table.red_target rY).trans (.head (table.step_coe (.const hc))
      ((table.red_const rX).tail (table.step_const (.method hc))))
  constOther := by
    intro n X Y d w c hc rY rX form ne
    have pre : WhRed V.rules V.roles (coeApp N.coe X Y d)
        (appSpine (.const N.coeConst) [.const c, w, d]) :=
      (table.red_target rY).trans (.head (table.step_coe (.const hc)) (table.red_const rX))
    rcases ValueSide.TypeForm.split laws form with hw | ⟨dw, nw⟩
    · exact ⟨_, pre.tail (table.step_const (.star hw ne)), .star⟩
    · exact ⟨_, pre, table.daimonic_const dw nw⟩
  pi := by
    intro n X Y d A A' B B' rY rX
    refine ⟨piBody N.coe A' (.lam B') A B d, ?_, fun ρ a => ?_⟩
    · exact (table.red_target rY).trans (.head (table.step_coe .pi)
        ((table.red_pi rX).tail (table.step_pi .lam)))
    · rw [inst0_rename_piBody]
      exact .single table.step_target_beta
  piOther := by
    intro n X Y d w A' B' rY rX form notPi
    have pre : WhRed V.rules V.roles (coeApp N.coe X Y d)
        (appSpine (.const N.coePi) [A', .lam B', w, d]) :=
      (table.red_target rY).trans (.head (table.step_coe .pi) (table.red_pi rX))
    rcases ValueSide.TypeForm.split laws form with hw | ⟨dw, nw⟩
    · exact ⟨_, pre.tail (table.step_pi (.star hw notPi)), .star⟩
    · exact ⟨_, pre, table.daimonic_pi dw nw⟩
  sigma := by
    intro n X Y p A A' B B' rY rX
    refine ⟨coeApp N.coe (inst0 (.fst p) B) (.app (.lam B') (coeApp N.coe A A' (.fst p)))
      (.snd p), ?_, .single table.step_target_beta⟩
    exact (table.red_target rY).trans (.head (table.step_coe .sigma)
      ((table.red_sigma rX).tail (table.step_sigma .pair)))
  sigmaOther := by
    intro n X Y d w A' B' rY rX form notSigma
    have pre : WhRed V.rules V.roles (coeApp N.coe X Y d)
        (appSpine (.const N.coeSigma) [A', .lam B', w, d]) :=
      (table.red_target rY).trans (.head (table.step_coe .sigma) (table.red_sigma rX))
    rcases ValueSide.TypeForm.split laws form with hw | ⟨dw, nw⟩
    · exact ⟨_, pre.tail (table.step_sigma (.star hw notSigma)), .star⟩
    · exact ⟨_, pre, table.daimonic_sigma dw nw⟩
  method := by
    intro n X Y d w rY form
    exact (table.red_target rY).tail (table.step_coe (ValueSide.MethodForm.coeTarget laws N form))
  stuck := by
    intro n X Y d w rY daimonic
    rcases daimonic.headForm_or_not laws.star with hw | nw
    · exact .inl ((table.red_target rY).tail
        (table.step_coe (.method (ValueSide.methodTarget_of_daimonic laws daimonic hw))))
    · exact .inr ⟨_, table.red_target rY, table.daimonic_coe daimonic nw⟩

end CoeTable

end Realizability
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
