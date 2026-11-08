import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Polymorphic

/-!
# Open structural formals: fold inversion and discharged arguments

A formal with type variables, as `(List $a)`, is checked by HE at each call by
unifying a typing of the argument with a fresh copy of it, and by PeTTa as
"typed once at some closed instance". Two of CeTTa's rules read such formals
statically.

**Unifiers.** CeTTa reads two types apart, each with its own variables, and
unifies them. A most general unifier that every ground unifier factors through
(`IsMGU`) has a semantic content (`bind_of_mgu`): every ground unifier sends a
term and its image under the unifier to the same type. A unifier of two terms
read apart gives them a common ground instance (`common_instance_of_unifier`).

**Fold inversion at every instance** (`prepared_pure_recognize_fold`). A typed
head with formal `F` folds over a constructor whose only row is
`(-> T₁ … Tₘ R)` when the row's range, unified with `F`, sends the recursive
field `Tᵣ` to `F` itself, variables included. Its content (`OpenInversion`):
whenever the range under the row's assignment is the formal under the formal's,
the recursive field's declared type is that same instance
(`openInversion_of_mgu`).
* *HE* (`field_static_of_open`, `spine_static`, `spine_calls_meet`): a cell
  typable at an instance of the formal types its recursive field at that
  instance, or the field has no typing; so along a spine every call the
  equations make to themselves passes HE's check, at the outer call's instance.
* *PeTTa* (`polyHolds_field`, `open_fold_eq_protocol`): a value typed once at
  some instance of the formal has its recursive field typed once at the same
  instance, and the typed protocol at the private formal, every call to itself
  checked, has exactly the machine's answers at every fuel past the spine's
  length, generalizing `RecognizedFolds.typed_fold_eq_protocol` to open
  formals; at a closed formal the condition gives round one's
  `RecognizedFolds.Inversion` (`inversion_of_open`).
* *Controls*: `Cons` at `(List $a)` inverts, through the unifier CeTTa computes
  (`Controls.cons_inverts`); `(: Bad (-> $a (List Number) (List $a)))` does not:
  its range meets `(List $t)` at `(List String)` where its recursive field is
  `(List Number)` (`Controls.bad_not_inverted`), and CeTTa's check of it fails
  (`Controls.bad_check_fails`).

**Discharged arguments** (`prepared_pure_discharged_arguments`). An argument at
an open formal is left unchecked where every member of its typing set unifies
with a fresh copy of the formal. HE's check at an open formal
(`MeetsOpen`): the argument has no typing, the formal is one HE does not check,
or a valid typing allows some instance of the formal. Every member allowing an
instance of the formal makes a covered argument meet it
(`meetsOpen_of_covers`); unification of the member and the formal read apart is
such an instance (`allowsInstance_of_unifier`). At a closed formal this is
round two's `InferredTypeSets.meets_of_lower` (`meetsOpen_lift`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFormals

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence InferredTypeSets RecognizedFolds

/-! ## Unifiers of terms read apart -/

/-- **A most general unifier**: `σ` unifies `s` and `t`, and every ground
unifier `ρ` of them is `σ` followed by `ρ`, as for the idempotent unifier a
syntactic unification computes with its bindings applied to their end. -/
def IsMGU {V : Type} (σ : V → Ty V) (s t : Ty V) : Prop :=
  s.bind σ = t.bind σ ∧ ∀ ρ : V → Ty Empty, s.bind ρ = t.bind ρ → ∀ x, (σ x).bind ρ = ρ x

/-- **What a most general unifier says**: a ground unifier sends any term and
its image under the unifier to the same type. -/
theorem bind_of_mgu {V : Type} {σ : V → Ty V} {s t : Ty V} (mgu : IsMGU σ s t)
    {ρ : V → Ty Empty} (hρ : s.bind ρ = t.bind ρ) (u : Ty V) : (u.bind σ).bind ρ = u.bind ρ := by
  rw [Ty.bind_bind]
  exact Ty.bind_congr u fun x _ => mgu.2 ρ hρ x

/-- Assignments of two terms read apart are one assignment of their union. -/
theorem bind_inl (θ φ : String → Ty Empty) (t : Ty String) :
    (t.map Sum.inl).bind (Sum.elim θ φ) = t.bind θ := by
  rw [Ty.bind_map]
  rfl

theorem bind_inr (θ φ : String → Ty Empty) (t : Ty String) :
    (t.map Sum.inr).bind (Sum.elim θ φ) = t.bind φ := by
  rw [Ty.bind_map]
  rfl

/-- **A unifier of two terms read apart gives a common ground instance.** -/
theorem common_instance_of_unifier {s t : Ty String} {σ : String ⊕ String → Ty (String ⊕ String)}
    (h : (s.map Sum.inl).bind σ = (t.map Sum.inr).bind σ) :
    ∃ θ φ : String → Ty Empty, s.bind θ = t.bind φ := by
  rw [Ty.bind_map, Ty.bind_map] at h
  have h' := congrArg (fun u : Ty (String ⊕ String) => u.bind fun _ => (default : Ty Empty)) h
  simp only [Ty.bind_bind] at h'
  exact ⟨_, _, h'⟩

/-! ## Fold inversion at every instance -/

/-- **The recursive field is the formal at every instance**: under any
assignment `θ` of the constructor row's variables and `φ` of the formal's that
send the row's range `R` and the formal `F` to one type, the recursive field's
declared type `T` goes to that type as well. -/
def OpenInversion (R T F : Ty String) : Prop :=
  ∀ θ φ : String → Ty Empty, R.bind θ = F.bind φ → T.bind θ = F.bind φ

/-- **CeTTa's check gives the inversion**: the row read with its own variables,
its range unified with the formal by a most general unifier, the recursive field
going to the formal itself, variables included. -/
theorem openInversion_of_mgu {R T F : Ty String} {σ : String ⊕ String → Ty (String ⊕ String)}
    (mgu : IsMGU σ (R.map Sum.inl) (F.map Sum.inr))
    (check : (T.map Sum.inl).bind σ = F.map Sum.inr) : OpenInversion R T F := by
  intro θ φ h
  have hρ : (R.map Sum.inl).bind (Sum.elim θ φ) = (F.map Sum.inr).bind (Sum.elim θ φ) := by
    rw [bind_inl, bind_inr]
    exact h
  have key := bind_of_mgu mgu hρ (T.map Sum.inl)
  rw [check, bind_inl, bind_inr] at key
  exact key.symm

/-- At a closed formal the inversion reads the formal itself. -/
theorem openInversion_lift_iff (R T : Ty String) (F : Ty Empty) :
    OpenInversion R T F.lift ↔ ∀ θ : String → Ty Empty, R.bind θ = F → T.bind θ = F := by
  simp only [OpenInversion, Ty.lift_bind_ground]
  exact ⟨fun h θ hθ => h θ (fun _ => default) hθ, fun h θ _ hθ => h θ hθ⟩

/-- A pair at one index of two lists is a pair of their zip. -/
theorem mem_zip_of_getElem? {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β} {k : ℕ} {a : α} {b : β},
      l₁[k]? = some a → l₂[k]? = some b → (a, b) ∈ l₁.zip l₂
  | [], _, _, _, _, h₁, _ => by simp at h₁
  | _ :: _, [], _, _, _, _, h₂ => by simp at h₂
  | x :: xs, y :: ys, 0, a, b, h₁, h₂ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
      subst h₁
      subst h₂
      simp
  | x :: xs, y :: ys, k + 1, a, b, h₁, h₂ => by
      simp only [List.getElem?_cons_succ] at h₁ h₂
      simp only [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ (mem_zip_of_getElem? h₁ h₂)

/-- The recursive field of a cell sits at index `pre` of its fields. -/
theorem getElem?_rest (s : Spec) (f : s.Fields) (r : Atom) : (f.1.1 ++ r :: f.1.2)[s.pre]? = some r := by
  rw [List.getElem?_append_right (by rw [f.2.1]), f.2.1, Nat.sub_self]
  rfl

/-! ### HE: a cell typed at an instance types its recursive field there

HE's check at an open formal is `InferredTypeSets.MeetsOpen`. -/

/-- A value statically at an instance of the formal meets it. -/
theorem meetsOpen_of_static {F : Ty String} {st : Stamp} {φ : String → Ty Empty}
    (h : StaticAt st (F.bind φ)) : MeetsOpen F st := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inr ⟨φ, h⟩)

/-- **A cell typable at an instance of the formal types its field at the same
instance**, where the field's declared type is the formal at every instance:
the field has no typing, or a valid typing allowing that instance. -/
theorem field_static_of_open {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)}
    {R : Ty String} (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {T : Ty String}
    {a : Atom} (hT : Ts[k]? = some T) (ha : args[k]? = some a) (checked : CheckedTy T)
    {F : Ty String} (inv : OpenInversion R T F) {φ : String → Ty Empty}
    (typed : Typable (stamp Γ (.expression (.symbol c :: args))) (F.bind φ)) :
    StaticAt (stamp Γ a) (F.bind φ) := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  obtain ⟨X, hX, hFX⟩ := typed
  rw [stamp_ctor Γ c ρ Ts R rows split] at hX
  by_cases len : Ts.length = args.length
  swap
  · simp [if_neg len] at hX
  simp only [if_pos len] at hX
  obtain ⟨Θ', -, -, hXe, each⟩ :=
    semCheck_ok_inv ρ R Ts _ Set.univ X ⟨fun _ => default, trivial⟩ hX
  subst hXe
  obtain ⟨θ, hθ, hRθ⟩ := hFX
  have hsa : (args.map (stamp Γ))[k]? = some (stamp Γ a) := by simp [ha]
  rcases forall₂_getElem? each hT hsa with h | h | ⟨Y, hY, hTY⟩
  · exact .inl h
  · rw [checked_stamp checked Γ a] at h
    cases h
  · refine .inr ⟨Y, hY, ?_⟩
    rw [← inv θ φ hRθ]
    exact hTY θ hθ

/-- An application of a constructor with one function row has a typing, valid
or an error. -/
theorem ctor_typs_ne_nil {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)}
    {R : Ty String} (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) :
    (stamp Γ (.expression (.symbol c :: args))).typs ≠ [] := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  rw [stamp_ctor Γ c ρ Ts R rows split]
  by_cases len : Ts.length = args.length
  · simp only [if_pos len]
    exact semCheck_ne_nil ρ R Ts _ Set.univ (by simpa using len)
  · simp [if_neg len]

section Spine

variable {Γ : Decls} (s : Spec) {ρ : Ty String} {Ts : List (Ty String)} {R T F : Ty String}

/-- **Along a spine every suffix is at the outer instance**: a spine of cells
typable at an instance of the formal has every suffix, its end included, at
that instance or without typing, when the recursive field is the formal at every
instance. -/
theorem spine_static (row : ctorRow Γ s.cons = some (ρ, Ts, R)) (hT : Ts[s.pre]? = some T)
    (checked : CheckedTy T) (inv : OpenInversion R T F) (φ : String → Ty Empty) (e : Atom) :
    ∀ fs : List s.Fields, Typable (stamp Γ (s.family.build ⟨fs, e⟩)) (F.bind φ) →
      ∀ i ≤ fs.length, StaticAt (stamp Γ (s.family.build ⟨fs.drop i, e⟩)) (F.bind φ)
  | [], typed, i, _ => by
      rw [List.drop_nil]
      exact .inr typed
  | f :: fs, typed, 0, _ => .inr typed
  | f :: fs, typed, i + 1, hi => by
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hi
      simp only [List.drop_succ_cons]
      have field : StaticAt (stamp Γ (s.family.build ⟨fs, e⟩)) (F.bind φ) :=
        field_static_of_open row _ hT (getElem?_rest s f _) checked inv typed
      cases fs with
      | nil =>
          simp only [List.length_nil, Nat.le_zero] at hi
          subst hi
          simpa using field
      | cons g gs =>
          refine spine_static row hT checked inv φ e (g :: gs) ?_ i hi
          rcases field with h | h
          · exact absurd h (ctor_typs_ne_nil row _)
          · exact h

/-- **Every call a typed fold makes to itself passes HE's check**: an argument
spine passing HE's check at the formal makes every recursive field along it,
the end included, pass the check too, at the outer call's instance. These are
the checks the recognized fold skips. -/
theorem spine_calls_meet (row : ctorRow Γ s.cons = some (ρ, Ts, R)) (hT : Ts[s.pre]? = some T)
    (checked : CheckedTy T) (checkedF : CheckedTy F) (inv : OpenInversion R T F) (e : Atom)
    (fs : List s.Fields) (outer : MeetsOpen F (stamp Γ (s.family.build ⟨fs, e⟩))) :
    ∀ i ≤ fs.length, MeetsOpen F (stamp Γ (s.family.build ⟨fs.drop i, e⟩)) := by
  cases fs with
  | nil =>
      intro i _
      simpa using outer
  | cons f gs =>
      rcases outer with h | h | ⟨φ, typed⟩
      · exact absurd h (ctor_typs_ne_nil row _)
      · rw [checked_stamp checkedF] at h
        cases h
      · intro i hi
        exact meetsOpen_of_static (spine_static s row hT checked inv φ e (f :: gs) typed i hi)

end Spine

/-! ### PeTTa: the protocol at a private formal -/

section PeTTa

variable {Γ : Decls} (grounded : String → Bool)

/-- **A value typed once at some instance of the formal has its recursive field
typed once at the same instance.** -/
theorem polyHolds_field (hΓ : Functional Γ) (s : Spec) {As : List (Ty String)} {Rc : Ty String}
    (row : Γ s.cons = [arrow As Rc]) (hlen : As.length = s.arity) {T : Ty String}
    (hT : As[s.pre]? = some T) (hTc : ¬ Unchecked T) {F : Ty String} (named : Named F)
    (inv : OpenInversion Rc T F) (f : s.Fields) (r : Atom) (h : PolyHolds Γ (s.cell f r) F) :
    PolyHolds Γ r F := by
  have len : (f.1.1 ++ r :: f.1.2).length = As.length := by rw [s.fields_length, hlen]
  obtain ⟨σ, σ', hσ, fields⟩ := poly_inversion hΓ row _ len F named h
  have hmem : (T, r) ∈ As.zip (f.1.1 ++ r :: f.1.2) := mem_zip_of_getElem? hT (getElem?_rest s f r)
  have typed := fields (T, r) hmem hTc
  rw [inv σ' σ hσ] at typed
  exact ⟨σ, typed⟩

/-- **At a closed formal the inversion is round one's**: the inversion of the
row gives `RecognizedFolds.Inversion`, the hypothesis of
`RecognizedFolds.typed_fold_eq_protocol`. -/
theorem inversion_of_open (hΓ : Functional Γ) (s : Spec) {As : List (Ty String)} {Rc : Ty String}
    (row : Γ s.cons = [arrow As Rc]) (hlen : As.length = s.arity) {T : Ty String}
    (hT : As[s.pre]? = some T) (hTc : ¬ Unchecked T) {F : Ty Empty} (named : Named F)
    (hm : ¬ MetaName F) (inv : OpenInversion Rc T F.lift) : RecognizedFolds.Inversion Γ grounded s F := by
  intro f r h
  have len : (f.1.1 ++ r :: f.1.2).length = As.length := by rw [s.fields_length, hlen]
  obtain ⟨σ, hσ, fields⟩ := ctor_inversion hΓ row _ len F named (h.count hm)
  have hmem : (T, r) ∈ As.zip (f.1.1 ++ r :: f.1.2) := mem_zip_of_getElem? hT (getElem?_rest s f r)
  have typed := fields (T, r) hmem hTc
  rw [(openInversion_lift_iff Rc T F).mp inv σ hσ] at typed
  exact Holds.of_count typed

/-- The protocol's run is the run whose every call runs the row's protocol. -/
theorem protocolRun_eq_factoredRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (row : Ty String) :
    ∀ n vs, protocolRun Γ grounded body row n vs =
      factoredRun (fun B vs => chainCall Γ (metatype grounded) B row vs) body n vs
  | 0, _ => rfl
  | n + 1, vs => by
      have ih : protocolRun Γ grounded body row n =
          factoredRun (fun B vs => chainCall Γ (metatype grounded) B row vs) body n :=
        funext fun ws => protocolRun_eq_factoredRun body row n ws
      simp only [protocolRun, factoredRun, ih]

/-- **A typed fold at an open formal answers as its protocol**: on an argument
typed once at some instance of the private formal `(c t₁ … tₖ)`, with the
recursive field's declared type that formal at every instance, the range typing
every integer once and the grounded operation answering integers, PeTTa's typed
protocol, every call to itself checked, has exactly the machine's answers at
every fuel past the argument's number of cells. -/
theorem open_fold_eq_protocol (hΓ : Functional Γ) (s : Spec) (wf : s.WF) (E : Env)
    (hE : PrimExact E s.op) {As : List (Ty String)} {Rc : Ty String} (row : Γ s.cons = [arrow As Rc])
    (hlen : As.length = s.arity) {T : Ty String} (hT : As[s.pre]? = some T) (hTc : ¬ Unchecked T)
    (ts : List (Ty String)) (named : Named (Ty.app ts)) (inv : OpenInversion Rc T (.app ts))
    (R : Ty Empty) (rg : ResultGuarded R.lift) (ints : ∀ z, Holds Γ grounded (int z) R)
    (primInts : ∀ vs w, w ∈ E.prim s.op.name vs → ∃ z, w = int z)
    (t : Atom) (ht : PolyHolds Γ t (.app ts)) (n : ℕ) (hn : s.cells t < n) :
    protocolRun Γ grounded (s.body E) (arrow [.app ts] R.lift) n [t] = machine s E n t := by
  rw [protocolRun_eq_factoredRun grounded, machine_eq_equations s wf E hE t n hn]
  have guarded : demand (Ty.app ts) = .guarded := by simp [demand, Unchecked]
  refine private_version_eq_protocol (Γ := Γ) (kind := metatype grounded) [.app ts] R
    (List.pairwise_singleton _ _) (Entry := fun vs => ∃ t', vs = [t'] ∧ PolyHolds Γ t' (.app ts))
    (Res := fun r => Holds Γ grounded r R) ?entry ?res ?calls ?results n [t] ⟨t, rfl, ht⟩
  case entry =>
    rintro vs ⟨t', rfl, ht'⟩
    simp only [argCountPoly, if_pos guarded, mul_one]
    rw [guardCountPoly_functional hΓ, if_pos ht']
  case res =>
    intro r hr
    rw [if_pos rg]
    exact hr.guardCount
  case calls =>
    rintro o o' agree - vs ⟨t', rfl, ht'⟩
    cases hu : s.uncell t' with
    | none =>
        by_cases hnil : t' = .symbol s.nil
        · subst hnil
          rw [s.body_nil, s.body_nil]
        · rw [s.body_other E o hu hnil, s.body_other E o' hu hnil]
    | some p =>
        obtain ⟨f, r⟩ := p
        rw [(s.uncell_eq_some).mp hu] at ht' ⊢
        have hr := polyHolds_field hΓ s row hlen hT hTc named inv f r ht'
        rw [s.body_cell E o wf f r, s.body_cell E o' wf f r, agree [r] ⟨r, rfl, hr⟩]
  case results =>
    rintro o - vs ⟨t', rfl, -⟩ w hw
    cases hu : s.uncell t' with
    | none =>
        by_cases hnil : t' = .symbol s.nil
        · subst hnil
          rw [s.body_nil, Multiset.mem_singleton] at hw
          subst hw
          exact ints s.base
        · rw [s.body_other E o hu hnil] at hw
          exact absurd hw (Multiset.notMem_zero w)
    | some p =>
        obtain ⟨f, r⟩ := p
        rw [(s.uncell_eq_some).mp hu, s.body_cell E o wf f r] at hw
        split_ifs at hw <;>
        · simp only [Multiset.mem_bind] at hw
          obtain ⟨_, _, _, _, hw⟩ := hw
          obtain ⟨z, rfl⟩ := primInts _ w hw
          exact ints z

end PeTTa

/-! ## Discharged arguments at open formals -/

/-- **The discharge at an open formal**: an argument covered by a typing set
whose every member allows an instance of the formal passes HE's check there. -/
theorem meetsOpen_of_covers {Γ : Decls} {Ms : List (Set (Ty Empty))} {v : Atom} {F : Ty String}
    (all : ∀ S ∈ Ms, AllowsInstance F S) (cov : Covers Γ (some Ms) v) : MeetsOpen F (stamp Γ v) := by
  obtain ⟨S, hS, hl⟩ := cov
  exact meetsOpen_of_lower (all S hS) hl

/-- **CeTTa's test is such an instance**: a member type and the formal, each
read with fresh variables, that unify allow a common ground instance. -/
theorem allowsInstance_of_unifier {M F : Ty String} {σ : String ⊕ String → Ty (String ⊕ String)}
    (h : (M.map Sum.inl).bind σ = (F.map Sum.inr).bind σ) : AllowsInstance F (inst M) := by
  obtain ⟨θ, φ, hθφ⟩ := common_instance_of_unifier h
  exact ⟨φ, θ, hθφ⟩

/-- **At a closed formal the discharge is round two's.** -/
theorem allowsInstance_lift_iff (F : Ty Empty) (S : Set (Ty Empty)) : AllowsInstance F.lift S ↔ F ∈ S := by
  simp only [AllowsInstance, Ty.lift_bind_ground]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun _ => default, h⟩⟩

/-! ## Controls -/

namespace Controls

/-- `(List $x)`. -/
abbrev listOf (x : Ty String) : Ty String := .app [.sym "List", x]

/-- The unifier CeTTa computes for `(List $a)` (the constructor's range, its
variable on the left) and `(List $t)` (the formal, on the right): `$a` bound to
`$t`. -/
def consUnifier : String ⊕ String → Ty (String ⊕ String) := fun x =>
  if x = .inl "a" then .var (.inr "t") else .var x

theorem consUnifier_mgu :
    IsMGU consUnifier ((listOf (.var "a")).map Sum.inl) ((listOf (.var "t")).map Sum.inr) := by
  refine ⟨by simp [consUnifier, Ty.map], fun ρ hρ x => ?_⟩
  simp only [Ty.map_app, List.map_cons, Ty.map_sym, Ty.map_var, List.map_nil, Ty.bind_app,
    Ty.bind_sym, Ty.bind_var', Ty.app.injEq, List.cons.injEq, true_and, and_true] at hρ
  by_cases hx : x = .inl "a"
  · subst hx
    simp only [consUnifier]
    exact hρ.symm
  · simp [consUnifier, hx]

/-- **`Cons` at `(List $t)` inverts**: its recursive field `(List $a)` goes to the
formal itself under the unifier, so the field is the formal at every instance. -/
theorem cons_inverts : OpenInversion (listOf (.var "a")) (listOf (.var "a")) (listOf (.var "t")) :=
  openInversion_of_mgu consUnifier_mgu (by simp [consUnifier, Ty.map])

/-- **`(: Bad (-> $a (List Number) (List $a)))` at `(List $t)` does not invert**:
its range meets the formal at `(List String)`, where its recursive field is
`(List Number)`. -/
theorem bad_not_inverted :
    ¬ OpenInversion (listOf (.var "a")) (listOf (.sym "Number")) (listOf (.var "t")) := by
  intro h
  have := h (fun _ => .sym "String") (fun _ => .sym "String") rfl
  simp at this

/-- **CeTTa's check of `Bad` fails**: under the unifier its recursive field is
`(List Number)`, not the formal. -/
theorem bad_check_fails :
    ((listOf (.sym "Number")).map Sum.inl).bind consUnifier ≠ (listOf (.var "t")).map Sum.inr := by
  simp [Ty.map]

/-- **A member unifying with the formal discharges it**: `(List $b)` unifies with
`(List $t)` read apart, so the member `Nil`'s typing gives allows an instance of
the formal. -/
theorem nil_allows : AllowsInstance (listOf (.var "t")) (inst (listOf (.var "b"))) :=
  allowsInstance_of_unifier (σ := fun x => if x = .inl "b" then .var (.inr "t") else .var x)
    (by simp [Ty.map])

/-- **A member that does not unify allows no instance**: `(List Number)` against
`(List String)`. -/
theorem number_list_not_string : ¬ AllowsInstance (listOf (.sym "String")) (inst (listOf (.sym "Number"))) := by
  rintro ⟨φ, θ, h⟩
  simp at h

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFormals
