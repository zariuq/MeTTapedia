import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# Syntactic elaboration of annotations

`elaborate` annotates the abstractions of a term by bidirectional elaboration, as the
kernel's annotation pass supplies the domain of every abstraction from the type
it is checked against:

* an abstraction checked against a dependent function type `Π (x : D). B` is
  annotated with `D`, and its body is checked against `B`;
* an abstraction in function position, `(λ x. b) a`, is annotated with the type
  the argument synthesizes;
* an application synthesizes the type of its function; when that type is a
  dependent function type, the argument is checked against its domain and the
  application synthesizes the instantiated codomain;
* a pair checked against a dependent pair type checks its components; the
  projections synthesize from the type of the pair; reflexivity checked against
  an identity type checks its point against the carrier;
* variables synthesize the type known for them, constants their declared type.

Types are compared syntactically and never reduced: where no type determines an
abstraction's domain it is annotated with `CTm.unknown`. Elaboration is total and
a section of erasure (`erase_elab`): it only adds annotations.

A rewrite schema is elaborated from its left side (`elabLeft`, `elabRight`): the
left side synthesizes its type from the declared type of its head, each
metavariable is given the type its position in the left side requires
(`patternKnowledge`), and the right side is elaborated against the left side's
type with that knowledge. A first-order left side (built from variables,
constants, heads, applications and reflexivity) has no abstraction, and its
elaboration is its only annotation (`elab_firstOrder`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-- The domain given to an abstraction whose domain no type determines. -/
def CTm.unknown {n : Nat} : CTm Head n := .const .anonymous

/-- What is known of the types of the variables of a context. -/
abbrev Knowledge (Head : Type) (n : Nat) := Fin n → Option (CTm Head n)

namespace Knowledge

/-- Nothing is known. -/
def empty {n : Nat} : Knowledge Head n := fun _ => none

/-- One more variable, of known or unknown type. -/
def cons {n : Nat} (type : Option (CTm Head n)) (K : Knowledge Head n) :
    Knowledge Head (n + 1) :=
  Fin.cases (type.map (CTm.rename wk)) fun i => (K i).map (CTm.rename wk)

/-- What the first of two sources knows, and otherwise what the second knows. -/
def merge {n : Nat} (K K' : Knowledge Head n) : Knowledge Head n := fun i =>
  match K i with
  | some T => some T
  | none => K' i

end Knowledge

/-- **Syntactic elaboration.** `elaborate decls K expected hint t` annotates the
abstractions of `t`, in a context whose variables have the types `K` knows and
whose constants have the declared types `decls`, checking `t` against `expected`
when it is given; `hint` is the type of the argument `t` is applied to. It
returns the annotated term and the type it synthesizes, if any. -/
def elaborate (decls : DeclName → Option (CTm Head 0)) :
    {n : Nat} → Knowledge Head n → Option (CTm Head n) → Option (CTm Head n) → Tm Head n →
      CTm Head n × Option (CTm Head n)
  | _, K, _, _, .var i => (.var i, K i)
  | _, _, _, _, .const c => (.const c, (decls c).map CTm.liftClosed)
  | _, _, _, _, .head h => (.head h, none)
  | _, K, _, _, .pi A B =>
      let A' := (elaborate decls K none none A).1
      (.pi A' (elaborate decls (K.cons (some A')) none none B).1, none)
  | _, K, _, _, .sigma A B =>
      let A' := (elaborate decls K none none A).1
      (.sigma A' (elaborate decls (K.cons (some A')) none none B).1, none)
  | _, K, _, _, .id A a b =>
      let A' := (elaborate decls K none none A).1
      (.id A' (elaborate decls K (some A') none a).1 (elaborate decls K (some A') none b).1, none)
  | _, K, expected, hint, .lam b =>
      match expected with
      | some (.pi D B) => (.lam D (elaborate decls (K.cons (some D)) (some B) none b).1, some (.pi D B))
      | _ =>
          match hint with
          | some D =>
              let b' := elaborate decls (K.cons (some D)) none none b
              (.lam D b'.1, b'.2.map (.pi D))
          | none => (.lam CTm.unknown (elaborate decls (K.cons none) none none b).1, none)
  | _, K, _, _, .app f a =>
      let f' := elaborate decls K none (elaborate decls K none none a).2 f
      match f'.2 with
      | some (.pi D B) =>
          let a' := (elaborate decls K (some D) none a).1
          (.app f'.1 a', some (CTm.inst0 a' B))
      | _ => (.app f'.1 (elaborate decls K none none a).1, none)
  | _, K, expected, _, .pair a b =>
      match expected with
      | some (.sigma A B) =>
          let a' := (elaborate decls K (some A) none a).1
          (.pair a' (elaborate decls K (some (CTm.inst0 a' B)) none b).1, some (.sigma A B))
      | _ => (.pair (elaborate decls K none none a).1 (elaborate decls K none none b).1, none)
  | _, K, _, _, .fst p =>
      let p' := elaborate decls K none none p
      match p'.2 with
      | some (.sigma A _) => (.fst p'.1, some A)
      | _ => (.fst p'.1, none)
  | _, K, _, _, .snd p =>
      let p' := elaborate decls K none none p
      match p'.2 with
      | some (.sigma _ B) => (.snd p'.1, some (CTm.inst0 (.fst p'.1) B))
      | _ => (.snd p'.1, none)
  | _, K, expected, _, .refl a =>
      match expected with
      | some (.id A x y) => (.refl (elaborate decls K (some A) none a).1, some (.id A x y))
      | _ =>
          let a' := elaborate decls K none none a
          (.refl a'.1, a'.2.map fun A => .id A a'.1 a'.1)

/-- **Elaboration only adds annotations**: it is a section of erasure. -/
@[simp] theorem erase_elab (decls : DeclName → Option (CTm Head 0)) {n : Nat} (t : Tm Head n)
    (K : Knowledge Head n) (expected hint : Option (CTm Head n)) :
    (elaborate decls K expected hint t).1.erase = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [elaborate, CTm.erase, ihA, ihB]
  | sigma A B ihA ihB => simp only [elaborate, CTm.erase, ihA, ihB]
  | id A a b ihA iha ihb => simp only [elaborate, CTm.erase, ihA, iha, ihb]
  | lam b ih =>
      simp only [elaborate]
      split
      · simp only [CTm.erase, ih]
      · split <;> simp only [CTm.erase, ih]
  | app f a ihf iha =>
      simp only [elaborate]
      split <;> simp only [CTm.erase, ihf, iha]
  | pair a b iha ihb =>
      simp only [elaborate]
      split <;> simp only [CTm.erase, iha, ihb]
  | fst p ih =>
      simp only [elaborate]
      split <;> simp only [CTm.erase, ih]
  | snd p ih =>
      simp only [elaborate]
      split <;> simp only [CTm.erase, ih]
  | refl a ih =>
      simp only [elaborate]
      split <;> simp only [CTm.erase, ih]

/-! ## Terms without abstractions -/

/-- Terms without abstractions. -/
def lamFree : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .const _ => true
  | _, .head _ => true
  | _, .pi A B => lamFree A && lamFree B
  | _, .sigma A B => lamFree A && lamFree B
  | _, .id A a b => lamFree A && lamFree a && lamFree b
  | _, .lam _ => false
  | _, .app f a => lamFree f && lamFree a
  | _, .pair a b => lamFree a && lamFree b
  | _, .fst p => lamFree p
  | _, .snd p => lamFree p
  | _, .refl a => lamFree a

/-- The annotation of a term in which every abstraction is annotated with
`CTm.unknown`: for a term without abstractions, its only annotation. -/
def liftTm {n : Nat} (t : Tm Head n) : CTm Head n := CTm.annotateWith CTm.unknown t

@[simp] theorem erase_liftTm {n : Nat} (t : Tm Head n) : (liftTm t).erase = t :=
  CTm.erase_annotateWith _ t

/-- The annotation of a context whose entries have no abstraction. -/
def liftCtx : {n : Nat} → Ctx Head n → CCtx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (liftCtx Γ) (liftTm A)

theorem liftTm_rename {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    liftTm (Presentation.rename ρ t) = (liftTm t).rename ρ := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
                      rw [ihA, ihB]
  | sigma A B ihA ihB => simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
                         rw [ihA, ihB]
  | id A a b ihA iha ihb =>
      simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
      rw [ihA, iha, ihb]
  | lam b ih =>
      simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
      rw [ih]
      rfl
  | app f a ihf iha =>
      simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
      rw [ihf, iha]
  | pair a b iha ihb =>
      simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
      rw [iha, ihb]
  | fst p ih => simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
                rw [ih]
  | snd p ih => simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
                rw [ih]
  | refl a ih => simp only [liftTm, CTm.annotateWith, Presentation.rename, CTm.rename] at *
                 rw [ih]

@[simp] theorem liftCtx_lookup {n : Nat} (Γ : Ctx Head n) (i : Fin n) :
    (liftCtx Γ).lookup i = liftTm (Ctx.lookup Γ i) := by
  induction Γ with
  | nil => exact i.elim0
  | snoc Γ A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (liftTm_rename wk A).symm
      · change ((liftCtx Γ).lookup j).rename wk = liftTm (Presentation.rename wk (Ctx.lookup Γ j))
        rw [ih, liftTm_rename]

/-- A term without abstractions has one annotation: elaboration adds none. -/
theorem elab_lamFree (decls : DeclName → Option (CTm Head 0)) {n : Nat} {t : Tm Head n}
    (lf : lamFree t = true) (K : Knowledge Head n) (expected hint : Option (CTm Head n)) :
    (elaborate decls K expected hint t).1 = liftTm t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | lam => cases lf
  | pi A B ihA ihB =>
      simp only [lamFree, Bool.and_eq_true] at lf
      simp only [elaborate, liftTm, CTm.annotateWith]
      rw [ihA lf.1, ihB lf.2]
      rfl
  | sigma A B ihA ihB =>
      simp only [lamFree, Bool.and_eq_true] at lf
      simp only [elaborate, liftTm, CTm.annotateWith]
      rw [ihA lf.1, ihB lf.2]
      rfl
  | id A a b ihA iha ihb =>
      simp only [lamFree, Bool.and_eq_true] at lf
      simp only [elaborate, liftTm, CTm.annotateWith]
      rw [ihA lf.1.1, iha lf.1.2, ihb lf.2]
      rfl
  | app f a ihf iha =>
      simp only [lamFree, Bool.and_eq_true] at lf
      simp only [elaborate]
      split <;> (simp only [liftTm, CTm.annotateWith]; rw [ihf lf.1, iha lf.2]; rfl)
  | pair a b iha ihb =>
      simp only [lamFree, Bool.and_eq_true] at lf
      simp only [elaborate]
      split <;> (simp only [liftTm, CTm.annotateWith]; rw [iha lf.1, ihb lf.2]; rfl)
  | fst p ih =>
      simp only [lamFree] at lf
      simp only [elaborate]
      split <;> (simp only [liftTm, CTm.annotateWith]; rw [ih lf]; rfl)
  | snd p ih =>
      simp only [lamFree] at lf
      simp only [elaborate]
      split <;> (simp only [liftTm, CTm.annotateWith]; rw [ih lf]; rfl)
  | refl a ih =>
      simp only [lamFree] at lf
      simp only [elaborate]
      split <;> (simp only [liftTm, CTm.annotateWith]; rw [ih lf]; rfl)

/-! ## First-order terms -/

/-- First-order terms: variables, constants, heads, applications and
reflexivity. They have no binder and no abstraction. -/
def firstOrder : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .const _ => true
  | _, .head _ => true
  | _, .app f a => firstOrder f && firstOrder a
  | _, .refl a => firstOrder a
  | _, _ => false

/-- A first-order term has one annotation: elaboration adds none. -/
theorem elab_firstOrder (decls : DeclName → Option (CTm Head 0)) {n : Nat} {t : Tm Head n}
    (fo : firstOrder t = true) (K : Knowledge Head n) (expected hint : Option (CTm Head n)) :
    (elaborate decls K expected hint t).1 = CTm.annotateWith CTm.unknown t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo
  | app f a ihf iha =>
      simp only [firstOrder, Bool.and_eq_true] at fo
      simp only [elaborate]
      split <;> simp only [CTm.annotateWith, ihf fo.1, iha fo.2]
  | refl a ih =>
      simp only [elaborate]
      split <;> simp only [CTm.annotateWith, ih fo]

/-! ## Elaboration of rewrite schemas -/

/-- The types the positions of a first-order left side require of its
metavariables: an argument position requires the domain of the type its
function synthesizes, and the point of reflexivity the carrier of the identity
type reflexivity is checked against. -/
def patternKnowledge (decls : DeclName → Option (CTm Head 0)) :
    {k : Nat} → Option (CTm Head k) → Tm Head k → Knowledge Head k
  | _, expected, .var i => fun j => if j = i then expected else none
  | _, _, .app f a =>
      let domain : Option (CTm Head _) :=
        match (elaborate decls Knowledge.empty none none f).2 with
        | some (.pi D _) => some D
        | _ => none
      (patternKnowledge decls none f).merge (patternKnowledge decls domain a)
  | _, expected, .refl a =>
      patternKnowledge decls
        (match expected with
          | some (.id A _ _) => some A
          | _ => none) a
  | _, _, _ => Knowledge.empty

/-- The equations the reflexivity positions of a first-order left side impose:
the point of a reflexivity proof checked against `Id A x y` equals `x` and `y`
at `A`, as triples (point, endpoint, carrier). -/
def patternEquations (decls : DeclName → Option (CTm Head 0)) :
    {k : Nat} → Option (CTm Head k) → Tm Head k → List (CTm Head k × CTm Head k × CTm Head k)
  | _, _, .app f a =>
      patternEquations decls none f ++
        patternEquations decls
          (match (elaborate decls Knowledge.empty none none f).2 with
            | some (.pi D _) => some D
            | _ => none) a
  | _, expected, .refl a =>
      (match expected with
        | some (.id A x y) => [(liftTm a, x, A), (liftTm a, y, A)]
        | _ => []) ++
      patternEquations decls
        (match expected with
          | some (.id A _ _) => some A
          | _ => none) a
  | _, _, _ => []

/-- The elaboration of the left side of a schema. -/
def elabLeft (decls : DeclName → Option (CTm Head 0)) {k : Nat} (L : Tm Head k) : CTm Head k :=
  (elaborate decls Knowledge.empty none none L).1

/-- The type the left side of a schema synthesizes. -/
def leftType (decls : DeclName → Option (CTm Head 0)) {k : Nat} (L : Tm Head k) :
    Option (CTm Head k) :=
  (elaborate decls Knowledge.empty none none L).2

/-- **The elaboration of the right side of a schema**, against the type of its
left side, with its metavariables typed as the left side requires. -/
def elabRight (decls : DeclName → Option (CTm Head 0)) {k : Nat} (L R : Tm Head k) :
    CTm Head k :=
  (elaborate decls (patternKnowledge decls none L) (leftType decls L) none R).1

@[simp] theorem erase_elabLeft (decls : DeclName → Option (CTm Head 0)) {k : Nat}
    (L : Tm Head k) : (elabLeft decls L).erase = L :=
  erase_elab decls L _ _ _

@[simp] theorem erase_elabRight (decls : DeclName → Option (CTm Head 0)) {k : Nat}
    (L R : Tm Head k) : (elabRight decls L R).erase = R :=
  erase_elab decls R _ _ _

theorem elabLeft_firstOrder (decls : DeclName → Option (CTm Head 0)) {k : Nat} {L : Tm Head k}
    (fo : firstOrder L = true) : elabLeft decls L = CTm.annotateWith CTm.unknown L :=
  elab_firstOrder decls fo _ _ _

/-! ## Declared types -/

/-- The elaboration of a closed term, in the empty context. -/
def elabClosed (decls : DeclName → Option (CTm Head 0)) (t : Tm Head 0) : CTm Head 0 :=
  (elaborate decls Knowledge.empty none none t).1

@[simp] theorem erase_elabClosed (decls : DeclName → Option (CTm Head 0)) (t : Tm Head 0) :
    (elabClosed decls t).erase = t :=
  erase_elab decls t _ _ _

/-- Declared types read without elaboration: every abstraction annotated with
`CTm.unknown`. Used only to elaborate the declared types themselves. -/
def naiveDeclarations (declared : DeclName → Option (Tm Head 0)) :
    DeclName → Option (CTm Head 0) :=
  fun c => (declared c).map (CTm.annotateWith CTm.unknown)

/-- **The elaborated declared types**: each declared type elaborated with the
declared types read as they are written. -/
def elabDeclarations (declared : DeclName → Option (Tm Head 0)) :
    DeclName → Option (CTm Head 0) :=
  fun c => (declared c).map (elabClosed (naiveDeclarations declared))

/-- A declared type without abstractions is elaborated to itself. -/
theorem elabDeclarations_lamFree (declared : DeclName → Option (Tm Head 0)) {c : DeclName}
    {T : Tm Head 0} (h : declared c = some T) (lf : lamFree T = true) :
    elabDeclarations declared c = some (liftTm T) := by
  simp only [elabDeclarations, h, Option.map_some, elabClosed, elab_lamFree _ lf]

theorem erase_elabDeclarations (declared : DeclName → Option (Tm Head 0)) (c : DeclName) :
    (elabDeclarations declared c).map CTm.erase = declared c := by
  unfold elabDeclarations
  cases declared c <;> simp

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
