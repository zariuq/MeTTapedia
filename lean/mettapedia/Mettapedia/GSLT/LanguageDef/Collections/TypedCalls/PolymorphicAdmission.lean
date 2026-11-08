import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Polymorphic

/-!
# PeTTa polymorphic heads on the prepared machine

CeTTa admits a PeTTa head whose signature has formals with type variables
(`prepared_pure_value_signature_formals`): a formal at which the trusted version
holds an instance fact is entered at that closed instance, the range read under
the instances; a formal whose variables no other position names (a private
formal) is checked as typed once at some closed instance; closed formals at
themselves. A call from outside enters the version where every check passes, and
otherwise keeps the signature's protocol.

* **The version on one instance** (`admitted_version_eq_protocol`): on
  arguments typed, under one instance, at every formal, the instance agreeing
  with the version's on the range, the signature's own protocol, its calls to
  itself included, has the version's answers at every fuel, when the version
  calls itself only on such arguments and its answers meet the range. This
  generalizes `instance_version_eq_protocol` (one fixed instance) to a family of
  instances free at the private formals.
* **The checks give one instance** (`checks_instance`): instance formals at the
  version's instance, private formals each at an instance of its own, combine
  into one instance of all the formals that is the version's on the range, as no
  private variable occurs anywhere else.
* **Dispatch is the protocol** (`dispatch_eq_protocol`): entering the version
  where the checks pass and running the protocol elsewhere answers as the
  protocol does on every argument; off the instance the version may not be
  entered (`Controls.build_off_instance`: the signature's protocol answers
  `(build 0 (Cons "a" Nil))`, the instance's answers nothing).
* **The hypotheses from the analysis** (`mixed_admission_eq_protocol`): for a
  head mixing instance and private formals, CeTTa's checks are the entry of the
  formals as the version reads them, instance formals at the version's instance
  (`checked_iff_entryPoly`), whose private formals share no variable
  (`privateParams_instantiated`); equations the analysis accepts there
  (`AcceptedPriv`) meet the hypotheses of `admission_eq_protocol`, so the
  dispatch is the signature's protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PolymorphicAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

variable {Γ : Decls} {grounded : String → Bool}

/-- **The version is the signature's protocol on admitted arguments**: on
arguments typed once under one instance of every formal that sends the range to
`Rθ`, with the version calling itself only on such arguments and answering at
`Rθ` whenever its calls to itself do, the protocol's run is the version's at
every fuel, and every answer meets `Rθ`. -/
theorem admitted_version_eq_protocol (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty String)} {R : Ty String} (Rθ : Ty Empty)
    (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R) (noMetaR : NoMeta R)
    {Entry : List Atom → Prop}
    (entry : ∀ vs, Entry vs → As.length = vs.length ∧ ∃ σ, AllTyped Γ As vs σ ∧ R.bind σ = Rθ)
    (calls : ∀ o o' : List Atom → Multiset Atom, (∀ ws, Entry ws → o ws = o' ws) →
      (∀ ws, Entry ws → ∀ r ∈ o ws, Holds Γ grounded r Rθ) → ∀ vs, Entry vs → bodyP o vs = bodyV o' vs)
    (results : ∀ o : List Atom → Multiset Atom, (∀ ws, Entry ws → ∀ r ∈ o ws, Holds Γ grounded r Rθ) →
      ∀ vs, Entry vs → ∀ r ∈ bodyV o vs, Holds Γ grounded r Rθ) :
    ∀ n vs, Entry vs → protocolRun Γ grounded bodyP (arrow As R) n vs = versionRun bodyV n vs ∧
      ∀ r ∈ versionRun bodyV n vs, Holds Γ grounded r Rθ
  | 0, _, _ => ⟨rfl, fun r hr => absurd hr (Multiset.notMem_zero r)⟩
  | n + 1, vs, hvs => by
      have ih := admitted_version_eq_protocol hΓ Rθ hAs hR noMetaR entry calls results n
      have agree : ∀ ws, Entry ws → protocolRun Γ grounded bodyP (arrow As R) n ws = versionRun bodyV n ws :=
        fun ws hws => (ih ws hws).1
      have oracle : ∀ ws, Entry ws → ∀ r ∈ versionRun bodyV n ws, Holds Γ grounded r Rθ :=
        fun ws hws => (ih ws hws).2
      have answers : ∀ r ∈ bodyV (versionRun bodyV n) vs, Holds Γ grounded r Rθ := results _ oracle vs hvs
      obtain ⟨len, σ, typed, hσ⟩ := entry vs hvs
      refine ⟨?_, answers⟩
      simp only [protocolRun, versionRun]
      rw [chainCall_shared hΓ grounded _ As R vs len hAs hR noMetaR,
        calls _ _ agree (fun ws hws r hr => by
          rw [agree ws hws] at hr
          exact oracle ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · have hm : ¬ MetaName Rθ := by
          rw [← hσ]
          exact noMetaR σ
        rw [if_pos ⟨σ, typed, by rw [hσ]; exact (answers r hr).count hm⟩]
      · rw [Multiset.bind_singleton, Multiset.map_id']

theorem forall₂_imp_mem {α β : Type} {P Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → (∀ a ∈ l₁, ∀ b, P a b → Q a b) →
      List.Forall₂ Q l₁ l₂
  | [], [], .nil, _ => .nil
  | a :: _, b :: _, .cons h rest, f =>
      .cons (f a (by simp) b h) (forall₂_imp_mem rest fun a' ha' => f a' (by simp [ha']))

/-- A formal with the check CeTTa makes there: at the version's instance, or,
private, at some instance of its own. -/
def Checked (θ : String → Ty Empty) (F : Ty String) (priv : Bool) (v : Atom) : Prop :=
  if priv then ∃ τ : String → Ty Empty, Holds Γ grounded v (F.bind τ) else Holds Γ grounded v (F.bind θ)

/-- No variable of a private formal occurs in another formal. -/
def PrivApart (Fs : List (Ty String × Bool)) : Prop :=
  Fs.Pairwise fun a b => (a.2 = true → ∀ x ∈ a.1.vars, x ∉ b.1.vars) ∧ (b.2 = true → ∀ x ∈ b.1.vars, x ∉ a.1.vars)

/-- The variables of the private formals. -/
def privVars (Fs : List (Ty String × Bool)) (x : String) : Prop := ∃ a ∈ Fs, a.2 = true ∧ x ∈ a.1.vars

/-- **The checks combine into one instance**: arguments passing CeTTa's checks
are typed under one instance of all the formals, the version's outside the
private formals' variables. -/
theorem checks_instance (θ : String → Ty Empty) :
    ∀ (Fs : List (Ty String × Bool)) (vs : List Atom), PrivApart Fs →
      List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs vs →
      ∃ σ : String → Ty Empty, (∀ x, ¬ privVars Fs x → σ x = θ x) ∧
        List.Forall₂ (fun a v => Holds Γ grounded v (a.1.bind σ)) Fs vs
  | [], [], _, .nil => ⟨θ, fun _ _ => rfl, .nil⟩
  | (F, p) :: Fs, v :: vs, apart, .cons hv hvs => by
      classical
      rw [PrivApart, List.pairwise_cons] at apart
      obtain ⟨σ', hσ', each⟩ := checks_instance θ Fs vs apart.2 hvs
      cases p with
      | false =>
          refine ⟨σ', fun x hx => hσ' x fun ⟨a, ha, hp, hxa⟩ => hx ⟨a, by simp [ha], hp, hxa⟩, .cons ?_ each⟩
          have hθ : Holds Γ grounded v (F.bind θ) := by simpa [Checked] using hv
          rw [Ty.bind_congr F fun x hx => hσ' x fun ⟨a, ha, hp, hxa⟩ =>
            ((apart.1 a ha).2 hp) x hxa hx]
          exact hθ
      | true =>
          obtain ⟨τ, hτ⟩ : ∃ τ : String → Ty Empty, Holds Γ grounded v (F.bind τ) := by
            simpa [Checked] using hv
          refine ⟨fun x => if x ∈ F.vars then τ x else σ' x, fun x hx => ?_, .cons ?_ ?_⟩
          · have hxF : x ∉ F.vars := fun h => hx ⟨(F, true), by simp, rfl, h⟩
            show (if x ∈ F.vars then τ x else σ' x) = θ x
            rw [if_neg hxF]
            exact hσ' x fun ⟨a, ha, hp, hxa⟩ => hx ⟨a, by simp [ha], hp, hxa⟩
          · rw [Ty.bind_congr F fun x hx => if_pos hx]
            exact hτ
          · refine forall₂_imp_mem each fun a ha w hw => ?_
            rw [Ty.bind_congr a.1 fun x hx => if_neg fun hF => (apart.1 a ha).1 rfl x hF hx]
            exact hw

/-- **Admitted arguments are typed under one instance sending the range to the
version's instance**, when no private variable occurs in the range. -/
theorem admitted_entry (θ : String → Ty Empty) (Fs : List (Ty String × Bool)) (R : Ty String)
    (vs : List Atom) (apart : PrivApart Fs)
    (rangeApart : ∀ a ∈ Fs, a.2 = true → ∀ x ∈ a.1.vars, x ∉ R.vars)
    (noMeta : ∀ a ∈ Fs, NoMeta a.1)
    (checks : List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs vs) :
    (Fs.map Prod.fst).length = vs.length ∧
      ∃ σ, AllTyped Γ (Fs.map Prod.fst) vs σ ∧ R.bind σ = R.bind θ := by
  obtain ⟨σ, hσ, each⟩ := checks_instance θ Fs vs apart checks
  refine ⟨by simpa using checks.length_eq, σ, ?_, ?_⟩
  · have each' : List.Forall₂ (fun F v => Holds Γ grounded v (F.bind σ) ∧ NoMeta F) (Fs.map Prod.fst) vs :=
      List.forall₂_map_left_iff.mpr (forall₂_imp_mem each fun a ha w hw => ⟨hw, noMeta a ha⟩)
    intro p hp
    have hpq := (List.forall₂_iff_zip.mp each').2 hp
    exact hpq.1.count (hpq.2 σ)
  · refine Ty.bind_congr R fun x hx => hσ x ?_
    rintro ⟨a, ha, hp, hxa⟩
    exact rangeApart a ha hp x hxa hx

open Classical in
/-- **The prepared dispatch**: the version where the entry checks pass, the
signature's protocol elsewhere. -/
noncomputable def dispatch (Entry : List Atom → Prop)
    (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom) (As : List (Ty String))
    (R : Ty String) (n : ℕ) (vs : List Atom) : Multiset Atom :=
  if Entry vs then versionRun bodyV n vs else protocolRun Γ grounded bodyP (arrow As R) n vs

/-- **Dispatch is the protocol** on every argument, at every fuel. -/
theorem dispatch_eq_protocol (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty String)} {R : Ty String} (Rθ : Ty Empty)
    (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R) (noMetaR : NoMeta R)
    {Entry : List Atom → Prop}
    (entry : ∀ vs, Entry vs → As.length = vs.length ∧ ∃ σ, AllTyped Γ As vs σ ∧ R.bind σ = Rθ)
    (calls : ∀ o o' : List Atom → Multiset Atom, (∀ ws, Entry ws → o ws = o' ws) →
      (∀ ws, Entry ws → ∀ r ∈ o ws, Holds Γ grounded r Rθ) → ∀ vs, Entry vs → bodyP o vs = bodyV o' vs)
    (results : ∀ o : List Atom → Multiset Atom, (∀ ws, Entry ws → ∀ r ∈ o ws, Holds Γ grounded r Rθ) →
      ∀ vs, Entry vs → ∀ r ∈ bodyV o vs, Holds Γ grounded r Rθ) (n : ℕ) (vs : List Atom) :
    dispatch (Γ := Γ) (grounded := grounded) Entry bodyP bodyV As R n vs =
      protocolRun Γ grounded bodyP (arrow As R) n vs := by
  classical
  unfold dispatch
  split_ifs with hvs
  · exact (admitted_version_eq_protocol hΓ Rθ hAs hR noMetaR entry calls results n vs hvs).1.symm
  · rfl

/-- **CeTTa's admission is the protocol**: with the entry its checks make
(instance formals at the version's instance, private formals each at an
instance of its own), and a version calling itself only on arguments passing
them, the dispatch answers as the signature's protocol on every argument. -/
theorem admission_eq_protocol (hΓ : Functional Γ) (θ : String → Ty Empty)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    (Fs : List (Ty String × Bool)) {R : Ty String} (apart : PrivApart Fs)
    (rangeApart : ∀ a ∈ Fs, a.2 = true → ∀ x ∈ a.1.vars, x ∉ R.vars)
    (hAs : ∀ A ∈ Fs.map Prod.fst, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R)
    (noMetaR : NoMeta R)
    (calls : ∀ o o' : List Atom → Multiset Atom,
      (∀ ws, List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs ws →
        o ws = o' ws) →
      (∀ ws, List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs ws →
        ∀ r ∈ o ws, Holds Γ grounded r (R.bind θ)) →
      ∀ vs, List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs vs →
        bodyP o vs = bodyV o' vs)
    (results : ∀ o : List Atom → Multiset Atom,
      (∀ ws, List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs ws →
        ∀ r ∈ o ws, Holds Γ grounded r (R.bind θ)) →
      ∀ vs, List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs vs →
        ∀ r ∈ bodyV o vs, Holds Γ grounded r (R.bind θ)) (n : ℕ) (vs : List Atom) :
    dispatch (Γ := Γ) (grounded := grounded)
        (List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs)
        bodyP bodyV (Fs.map Prod.fst) R n vs =
      protocolRun Γ grounded bodyP (arrow (Fs.map Prod.fst) R) n vs :=
  dispatch_eq_protocol hΓ (R.bind θ) hAs hR noMetaR
    (fun ws hws => admitted_entry θ Fs R ws apart rangeApart
      (fun a ha => (hAs a.1 (List.mem_map_of_mem ha)).2) hws) calls results n vs

/-- **Off the instance the version may not be entered**: the control of
`Polymorphic`, where the signature's protocol answers `(build 0 (Cons "a" Nil))`
and the instance's protocol does not; dispatch keeps the signature's protocol
there. -/
theorem off_instance_keeps_protocol (grounded : String → Bool) :
    count (info Controls.decls Controls.cellA) Controls.listNumber = 0 ∧
      protocolRun Controls.decls grounded Controls.buildBody
          (arrow [.sym "Number", Controls.listA] Controls.listA) 1
          [Controls.num 0, Controls.cellA] = {Controls.cellA} ∧
      protocolRun Controls.decls grounded Controls.buildBody
          (arrow ([Ty.sym "Number", Controls.listNumber].map Ty.lift) Controls.listNumber.lift) 1
          [Controls.num 0, Controls.cellA] = 0 :=
  Controls.build_off_instance grounded

/-! ## The version hypotheses from the analysis

A head mixing instance formals and private formals is analysed at the formals
as its version reads them (`instantiated`): an instance formal at the version's
instance, a private formal as written. CeTTa's checks at the entry are exactly
the entry of those formals (`checked_iff_entryPoly`), whose private formals share
no variable (`privateParams_instantiated`), so an analysis accepting the
equations there (`AcceptedPriv`, the facts read at every instance of the private
formals) gives the hypotheses `calls` and `results` of `admission_eq_protocol`
(`mixed_admission_eq_protocol`). -/

section Analysis

variable {res : String → Ty Empty} {ent : String → List (Ty Empty)}

/-- The formals as the version reads them: an instance formal at the version's
instance `θ`, a private formal as written. -/
def instantiated (θ : String → Ty Empty) (Fs : List (Ty String × Bool)) : List (Ty String) :=
  Fs.map fun a => if a.2 then a.1 else (a.1.bind θ).lift

/-- **CeTTa's checks are the entry of the instantiated formals.** -/
theorem checked_iff_entryPoly (θ : String → Ty Empty) :
    ∀ (Fs : List (Ty String × Bool)) (vs : List Atom), (∀ a ∈ Fs, demand a.1 = .guarded ∧ NoMeta a.1) →
      (List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs vs ↔
        EntryPoly Γ grounded (instantiated θ Fs) vs)
  | [], [], _ => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _, _ => ⟨fun h => (by cases h), fun h => (by simp [EntryPoly, instantiated] at h)⟩
  | _ :: _, [], _ => ⟨fun h => (by cases h), fun h => (by simp [EntryPoly, instantiated] at h)⟩
  | (F, p) :: Fs, v :: vs, hAs => by
      have rest := checked_iff_entryPoly θ Fs vs fun a ha => hAs a (by simp [ha])
      obtain ⟨hg, noMeta⟩ := hAs (F, p) (by simp)
      simp only [instantiated, List.map_cons] at rest ⊢
      rw [List.forall₂_cons, EntryPoly, List.forall₂_cons, ← EntryPoly, ← rest]
      refine and_congr ?_ Iff.rfl
      cases p with
      | true =>
          simp only [Checked, if_true]
          exact ⟨fun h _ => h, fun h => h hg⟩
      | false =>
          simp only [Checked, Bool.false_eq_true, if_false]
          rw [demand_bind_lift noMeta.not_var θ]
          refine ⟨fun h _ => ⟨fun _ => default, by rw [Ty.lift_bind_ground]; exact h⟩, fun h => ?_⟩
          obtain ⟨τ, hτ⟩ := h hg
          rwa [Ty.lift_bind_ground] at hτ

/-- **The instantiated formals share no variable**: a private formal's variables
are its own, and an instance formal has none. -/
theorem privateParams_instantiated (θ : String → Ty Empty) :
    ∀ Fs : List (Ty String × Bool), PrivApart Fs → PrivateParams (instantiated θ Fs)
  | [], _ => List.Pairwise.nil
  | (F, p) :: Fs, apart => by
      rw [PrivApart, List.pairwise_cons] at apart
      simp only [instantiated, List.map_cons, PrivateParams, List.pairwise_cons]
      refine ⟨fun B hB x hx hxB => ?_, privateParams_instantiated θ Fs apart.2⟩
      obtain ⟨⟨G, q⟩, hG, rfl⟩ := List.mem_map.mp hB
      cases p with
      | false => simp at hx
      | true =>
          simp only [if_true] at hx
          cases q with
          | true => exact (apart.1 (G, true) hG).1 rfl x hx hxB
          | false => simp at hxB

/-- **The admission of a head mixing instance and private formals, from the
analysis**: where every equation is accepted at the instantiated formals and the
range's instance, with the operations and the versions it enters answering what
the analysis assumes, CeTTa's dispatch (the version where the checks pass, the
protocol elsewhere) answers as the signature's protocol on every argument, at
every fuel. -/
theorem mixed_admission_eq_protocol (hΓ : Functional Γ) (θ : String → Ty Empty) {E : Env}
    {eqs : List Equation} (Fs : List (Ty String × Bool)) {R : Ty String} (apart : PrivApart Fs)
    (rangeApart : ∀ a ∈ Fs, a.2 = true → ∀ x ∈ a.1.vars, x ∉ R.vars)
    (hAs : ∀ A ∈ Fs.map Prod.fst, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R)
    (noMetaR : NoMeta R) (acc : ∀ eq ∈ eqs, AcceptedPriv Γ res ent (instantiated θ Fs) (R.bind θ) eq)
    (hE : EnvOK Γ grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    (n : ℕ) (vs : List Atom) :
    dispatch (Γ := Γ) (grounded := grounded)
        (List.Forall₂ (fun a v => Checked (Γ := Γ) (grounded := grounded) θ a.1 a.2 v) Fs)
        (fun o => equationsBody E eqs ⟨o, enP⟩) (fun o => equationsBody E eqs ⟨o, enV⟩)
        (Fs.map Prod.fst) R n vs =
      protocolRun Γ grounded (fun o => equationsBody E eqs ⟨o, enP⟩) (arrow (Fs.map Prod.fst) R) n vs := by
  have hAs' : ∀ a ∈ Fs, demand a.1 = .guarded ∧ NoMeta a.1 :=
    fun a ha => hAs a.1 (List.mem_map_of_mem ha)
  have iff := checked_iff_entryPoly (Γ := Γ) (grounded := grounded) θ Fs
  have priv := privateParams_instantiated θ Fs apart
  refine admission_eq_protocol hΓ θ Fs apart rangeApart hAs hR noMetaR ?_ ?_ n vs
  · intro o o' agree oracle ws hws
    obtain ⟨σ, hσ⟩ := entryPoly_instance priv ((iff ws hAs').mp hws)
    unfold equationsBody
    refine Multiset.bind_congr fun eq heq => ?_
    split
    · next ρ hm =>
        exact eval_congr hΓ hE
          ⟨fun ws' h' r hr => oracle ws' ((iff ws' hAs').mpr h') r hr,
            fun f ws' h' r hr => enRes f ws' h' r (enAgree f ws' h' ▸ hr)⟩
          ⟨fun ws' h' => agree ws' ((iff ws' hAs').mpr h'), enAgree⟩ eq.rhs ρ
          (eqFacts_sound hΓ (acc eq heq).linear hm hσ) ((acc eq heq).calls σ)
    · rfl
  · intro o oracle ws hws r hr
    obtain ⟨σ, hσ⟩ := entryPoly_instance priv ((iff ws hAs').mp hws)
    unfold equationsBody at hr
    obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
    split at hr
    · next ρ hm =>
        exact eval_sound hΓ hE ⟨fun ws' h' r hr => oracle ws' ((iff ws' hAs').mpr h') r hr, enRes⟩
          eq.rhs ρ (eqFacts_sound hΓ (acc eq heq).linear hm hσ) (R.bind θ) ((acc eq heq).result σ)
          ((acc eq heq).calls σ) r hr
    · exact absurd hr (Multiset.notMem_zero r)

end Analysis

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PolymorphicAdmission
