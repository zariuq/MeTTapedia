import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-!
# Structural laws for the shared presentation grammar

`Presentation.Tm` is parameterized by its universe heads.  Its renaming and
substitution algebra is therefore independent of the Legacy/Tower choice and
is proved once here.  These laws are the binding substrate used by universe
codes and schema elaboration.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-! ## Renaming laws -/

@[simp] theorem liftRen_id : liftRen (idRen (n := n)) = idRen := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem liftRen_comp_apply (rhoTwo : Ren m k) (rhoOne : Ren n m)
    (i : Fin (n + 1)) :
    liftRen rhoTwo (liftRen rhoOne i) =
      liftRen (fun j => rhoTwo (rhoOne j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem liftRen_ext {rho xi : Ren n m}
    (equal : ∀ i, rho i = xi i) :
    ∀ i : Fin (n + 1), liftRen rho i = liftRen xi i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [liftRen, equal j]

theorem rename_ext {rho xi : Ren n m} (equal : ∀ i, rho i = xi i) :
    ∀ term : Tm Head n, rename rho term = rename xi term := by
  intro term
  induction term generalizing m with
  | var i => simp [rename, equal i]
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain (rho := rho) (xi := xi) equal]
      exact ihCodomain (rho := liftRen rho) (xi := liftRen xi)
        (liftRen_ext equal)
  | sigma domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain (rho := rho) (xi := xi) equal]
      exact ihCodomain (rho := liftRen rho) (xi := liftRen xi)
        (liftRen_ext equal)
  | id type left right ihType ihLeft ihRight =>
      simp [rename, ihType (rho := rho) (xi := xi) equal,
        ihLeft (rho := rho) (xi := xi) equal,
        ihRight (rho := rho) (xi := xi) equal]
  | lam body ih =>
      simp [rename]
      exact ih (rho := liftRen rho) (xi := liftRen xi) (liftRen_ext equal)
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction (rho := rho) (xi := xi) equal,
        ihArgument (rho := rho) (xi := xi) equal]
  | pair first second ihFirst ihSecond =>
      simp [rename, ihFirst (rho := rho) (xi := xi) equal,
        ihSecond (rho := rho) (xi := xi) equal]
  | fst pair ih => simpa [rename] using ih (rho := rho) (xi := xi) equal
  | snd pair ih => simpa [rename] using ih (rho := rho) (xi := xi) equal
  | refl term ih => simpa [rename] using ih (rho := rho) (xi := xi) equal

@[simp] theorem rename_id : ∀ term : Tm Head n, rename idRen term = term := by
  intro term
  induction term with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain, ihCodomain]
  | id type left right ihType ihLeft ihRight =>
      simp [rename, ihType, ihLeft, ihRight]
  | lam body ih => simp [rename, ih]
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction, ihArgument]
  | pair first second ihFirst ihSecond =>
      simp [rename, ihFirst, ihSecond]
  | fst pair ih => simp [rename, ih]
  | snd pair ih => simp [rename, ih]
  | refl term ih => simp [rename, ih]

@[simp] theorem rename_comp :
    ∀ {n m k} (rhoTwo : Ren m k) (rhoOne : Ren n m) (term : Tm Head n),
      rename rhoTwo (rename rhoOne term) =
        rename (fun i => rhoTwo (rhoOne i)) term := by
  intro n m k rhoTwo rhoOne term
  induction term generalizing m k rhoTwo with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain (rhoTwo := rhoTwo) (rhoOne := rhoOne)]
      calc
        rename (liftRen rhoTwo) (rename (liftRen rhoOne) codomain) =
            rename (fun i => liftRen rhoTwo (liftRen rhoOne i)) codomain := by
              simpa using ihCodomain
                (rhoTwo := liftRen rhoTwo) (rhoOne := liftRen rhoOne)
        _ = rename (liftRen (fun i => rhoTwo (rhoOne i))) codomain := by
              exact rename_ext
                (rho := fun i => liftRen rhoTwo (liftRen rhoOne i))
                (xi := liftRen (fun i => rhoTwo (rhoOne i)))
                (fun i => liftRen_comp_apply rhoTwo rhoOne i) codomain
  | sigma domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain (rhoTwo := rhoTwo) (rhoOne := rhoOne)]
      calc
        rename (liftRen rhoTwo) (rename (liftRen rhoOne) codomain) =
            rename (fun i => liftRen rhoTwo (liftRen rhoOne i)) codomain := by
              simpa using ihCodomain
                (rhoTwo := liftRen rhoTwo) (rhoOne := liftRen rhoOne)
        _ = rename (liftRen (fun i => rhoTwo (rhoOne i))) codomain := by
              exact rename_ext
                (rho := fun i => liftRen rhoTwo (liftRen rhoOne i))
                (xi := liftRen (fun i => rhoTwo (rhoOne i)))
                (fun i => liftRen_comp_apply rhoTwo rhoOne i) codomain
  | id type left right ihType ihLeft ihRight =>
      simp [rename, ihType (rhoTwo := rhoTwo) (rhoOne := rhoOne),
        ihLeft (rhoTwo := rhoTwo) (rhoOne := rhoOne),
        ihRight (rhoTwo := rhoTwo) (rhoOne := rhoOne)]
  | lam body ih =>
      simp [rename]
      calc
        rename (liftRen rhoTwo) (rename (liftRen rhoOne) body) =
            rename (fun i => liftRen rhoTwo (liftRen rhoOne i)) body := by
              simpa using ih
                (rhoTwo := liftRen rhoTwo) (rhoOne := liftRen rhoOne)
        _ = rename (liftRen (fun i => rhoTwo (rhoOne i))) body := by
              exact rename_ext
                (rho := fun i => liftRen rhoTwo (liftRen rhoOne i))
                (xi := liftRen (fun i => rhoTwo (rhoOne i)))
                (fun i => liftRen_comp_apply rhoTwo rhoOne i) body
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction (rhoTwo := rhoTwo) (rhoOne := rhoOne),
        ihArgument (rhoTwo := rhoTwo) (rhoOne := rhoOne)]
  | pair first second ihFirst ihSecond =>
      simp [rename, ihFirst (rhoTwo := rhoTwo) (rhoOne := rhoOne),
        ihSecond (rhoTwo := rhoTwo) (rhoOne := rhoOne)]
  | fst pair ih =>
      simpa [rename] using ih (rhoTwo := rhoTwo) (rhoOne := rhoOne)
  | snd pair ih =>
      simpa [rename] using ih (rhoTwo := rhoTwo) (rhoOne := rhoOne)
  | refl term ih =>
      simpa [rename] using ih (rhoTwo := rhoTwo) (rhoOne := rhoOne)

/-! ## Substitution laws -/

@[simp] theorem subst0_zero (term : Tm Head n) :
    subst0 term 0 = term := rfl

@[simp] theorem subst0_succ (term : Tm Head n) (i : Fin n) :
    subst0 term i.succ = .var i := rfl

@[simp] theorem inst0_var_zero (term : Tm Head n) :
    inst0 term (.var 0) = term := rfl

@[simp] theorem inst0_var_succ (term : Tm Head n) (i : Fin n) :
    inst0 term (.var i.succ) = .var i := rfl

@[simp] theorem subst_var (sigma : Sub Head n m) (i : Fin n) :
    subst sigma (.var i) = sigma i := rfl

@[simp] theorem liftSub_zero (sigma : Sub Head n m) :
    liftSub sigma 0 = (.var 0 : Tm Head (m + 1)) := rfl

@[simp] theorem liftSub_succ (sigma : Sub Head n m) (i : Fin n) :
    liftSub sigma i.succ = rename wk (sigma i) := rfl

theorem subst_ext {sigma tau : Sub Head n m}
    (equal : ∀ i, sigma i = tau i) :
    ∀ term : Tm Head n, subst sigma term = subst tau term := by
  intro term
  induction term generalizing m with
  | var i => simp [subst, equal i]
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain (sigma := sigma) (tau := tau) equal]
      exact ihCodomain (sigma := liftSub sigma) (tau := liftSub tau) (by
        intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          simp [liftSub, equal j])
  | sigma domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain (sigma := sigma) (tau := tau) equal]
      exact ihCodomain (sigma := liftSub sigma) (tau := liftSub tau) (by
        intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          simp [liftSub, equal j])
  | id type left right ihType ihLeft ihRight =>
      simp [subst, ihType (sigma := sigma) (tau := tau) equal,
        ihLeft (sigma := sigma) (tau := tau) equal,
        ihRight (sigma := sigma) (tau := tau) equal]
  | lam body ih =>
      simp [subst]
      exact ih (sigma := liftSub sigma) (tau := liftSub tau) (by
        intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          simp [liftSub, equal j])
  | app function argument ihFunction ihArgument =>
      simp [subst, ihFunction (sigma := sigma) (tau := tau) equal,
        ihArgument (sigma := sigma) (tau := tau) equal]
  | pair first second ihFirst ihSecond =>
      simp [subst, ihFirst (sigma := sigma) (tau := tau) equal,
        ihSecond (sigma := sigma) (tau := tau) equal]
  | fst pair ih => simpa [subst] using ih (sigma := sigma) (tau := tau) equal
  | snd pair ih => simpa [subst] using ih (sigma := sigma) (tau := tau) equal
  | refl term ih => simpa [subst] using ih (sigma := sigma) (tau := tau) equal

@[simp] theorem liftSub_ids : liftSub (ids (Head := Head) (n := n)) = ids := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem subst_ids : ∀ term : Tm Head n, subst ids term = term := by
  intro term
  induction term with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain, ihCodomain]
  | id type left right ihType ihLeft ihRight =>
      simp [subst, ihType, ihLeft, ihRight]
  | lam body ih => simp [subst, ih]
  | app function argument ihFunction ihArgument =>
      simp [subst, ihFunction, ihArgument]
  | pair first second ihFirst ihSecond =>
      simp [subst, ihFirst, ihSecond]
  | fst pair ih => simp [subst, ih]
  | snd pair ih => simp [subst, ih]
  | refl term ih => simp [subst, ih]

@[simp] theorem rename_liftSub (rho : Ren m k) (sigma : Sub Head n m)
    (i : Fin (n + 1)) :
    rename (liftRen rho) (liftSub sigma i) =
      liftSub (fun j => rename rho (sigma j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    calc
      rename (liftRen rho) (liftSub sigma j.succ) =
          rename (liftRen rho) (rename wk (sigma j)) := by rfl
      _ = rename (fun x => liftRen rho (wk x)) (sigma j) := by
            simp [rename_comp]
      _ = rename (fun x => wk (rho x)) (sigma j) := by
            exact rename_ext
              (rho := fun x => liftRen rho (wk x))
              (xi := fun x => wk (rho x))
              (by intro x; simp [wk, liftRen]) (sigma j)
      _ = rename wk (rename rho (sigma j)) := by simp [rename_comp]
      _ = liftSub (fun x => rename rho (sigma x)) j.succ := by rfl

theorem rename_subst :
    ∀ {n m k} (rho : Ren m k) (sigma : Sub Head n m) (term : Tm Head n),
      rename rho (subst sigma term) =
        subst (fun i => rename rho (sigma i)) term := by
  intro n m k rho sigma term
  induction term generalizing m k rho with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [rename, subst, ihDomain (rho := rho) (sigma := sigma)]
      calc
        rename (liftRen rho) (subst (liftSub sigma) codomain) =
            subst (fun i => rename (liftRen rho) (liftSub sigma i)) codomain := by
              simpa using ihCodomain
                (rho := liftRen rho) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => rename rho (sigma i))) codomain := by
              apply subst_ext
              intro i
              exact rename_liftSub rho sigma i
  | sigma domain codomain ihDomain ihCodomain =>
      simp [rename, subst, ihDomain (rho := rho) (sigma := sigma)]
      calc
        rename (liftRen rho) (subst (liftSub sigma) codomain) =
            subst (fun i => rename (liftRen rho) (liftSub sigma i)) codomain := by
              simpa using ihCodomain
                (rho := liftRen rho) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => rename rho (sigma i))) codomain := by
              apply subst_ext
              intro i
              exact rename_liftSub rho sigma i
  | id type left right ihType ihLeft ihRight =>
      simp [rename, subst, ihType (rho := rho) (sigma := sigma),
        ihLeft (rho := rho) (sigma := sigma),
        ihRight (rho := rho) (sigma := sigma)]
  | lam body ih =>
      simp [rename, subst]
      calc
        rename (liftRen rho) (subst (liftSub sigma) body) =
            subst (fun i => rename (liftRen rho) (liftSub sigma i)) body := by
              simpa using ih (rho := liftRen rho) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => rename rho (sigma i))) body := by
              apply subst_ext
              intro i
              exact rename_liftSub rho sigma i
  | app function argument ihFunction ihArgument =>
      simp [rename, subst, ihFunction (rho := rho) (sigma := sigma),
        ihArgument (rho := rho) (sigma := sigma)]
  | pair first second ihFirst ihSecond =>
      simp [rename, subst, ihFirst (rho := rho) (sigma := sigma),
        ihSecond (rho := rho) (sigma := sigma)]
  | fst pair ih => simpa [rename, subst] using ih (rho := rho) (sigma := sigma)
  | snd pair ih => simpa [rename, subst] using ih (rho := rho) (sigma := sigma)
  | refl term ih => simpa [rename, subst] using ih (rho := rho) (sigma := sigma)

@[simp] theorem liftSub_liftRen_apply (sigma : Sub Head m k)
    (rho : Ren n m) (i : Fin (n + 1)) :
    liftSub sigma (liftRen rho i) =
      liftSub (fun j => sigma (rho j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem subst_rename :
    ∀ {n m k} (sigma : Sub Head m k) (rho : Ren n m) (term : Tm Head n),
      subst sigma (rename rho term) =
        subst (fun i => sigma (rho i)) term := by
  intro n m k sigma rho term
  induction term generalizing m k sigma with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [subst, rename, ihDomain (sigma := sigma) (rho := rho)]
      calc
        subst (liftSub sigma) (rename (liftRen rho) codomain) =
            subst (fun i => liftSub sigma (liftRen rho i)) codomain := by
              simpa using ihCodomain
                (sigma := liftSub sigma) (rho := liftRen rho)
        _ = subst (liftSub (fun i => sigma (rho i))) codomain := by
              apply subst_ext
              intro i
              exact liftSub_liftRen_apply sigma rho i
  | sigma domain codomain ihDomain ihCodomain =>
      simp [subst, rename, ihDomain (sigma := sigma) (rho := rho)]
      calc
        subst (liftSub sigma) (rename (liftRen rho) codomain) =
            subst (fun i => liftSub sigma (liftRen rho i)) codomain := by
              simpa using ihCodomain
                (sigma := liftSub sigma) (rho := liftRen rho)
        _ = subst (liftSub (fun i => sigma (rho i))) codomain := by
              apply subst_ext
              intro i
              exact liftSub_liftRen_apply sigma rho i
  | id type left right ihType ihLeft ihRight =>
      simp [subst, rename, ihType (sigma := sigma) (rho := rho),
        ihLeft (sigma := sigma) (rho := rho),
        ihRight (sigma := sigma) (rho := rho)]
  | lam body ih =>
      simp [subst, rename]
      calc
        subst (liftSub sigma) (rename (liftRen rho) body) =
            subst (fun i => liftSub sigma (liftRen rho i)) body := by
              simpa using ih (sigma := liftSub sigma) (rho := liftRen rho)
        _ = subst (liftSub (fun i => sigma (rho i))) body := by
              apply subst_ext
              intro i
              exact liftSub_liftRen_apply sigma rho i
  | app function argument ihFunction ihArgument =>
      simp [subst, rename, ihFunction (sigma := sigma) (rho := rho),
        ihArgument (sigma := sigma) (rho := rho)]
  | pair first second ihFirst ihSecond =>
      simp [subst, rename, ihFirst (sigma := sigma) (rho := rho),
        ihSecond (sigma := sigma) (rho := rho)]
  | fst pair ih => simpa [subst, rename] using ih (sigma := sigma) (rho := rho)
  | snd pair ih => simpa [subst, rename] using ih (sigma := sigma) (rho := rho)
  | refl term ih => simpa [subst, rename] using ih (sigma := sigma) (rho := rho)

@[simp] theorem subst_liftSub_wk (sigma : Sub Head n m) (term : Tm Head n) :
    subst (liftSub sigma) (rename wk term) =
      rename wk (subst sigma term) := by
  calc
    subst (liftSub sigma) (rename wk term) =
        subst (fun i => liftSub sigma (wk i)) term := by
          simpa using subst_rename (sigma := liftSub sigma) (rho := wk)
            (term := term)
    _ = subst (fun i => rename wk (sigma i)) term := by rfl
    _ = rename wk (subst sigma term) := by
          symm
          simpa using rename_subst (rho := wk) (sigma := sigma) (term := term)

@[simp] theorem liftSub_comp_apply (tau : Sub Head m k)
    (sigma : Sub Head n m) (i : Fin (n + 1)) :
    subst (liftSub tau) (liftSub sigma i) =
      liftSub (fun x => subst tau (sigma x)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    calc
      subst (liftSub tau) (liftSub sigma j.succ) =
          subst (liftSub tau) (rename wk (sigma j)) := by rfl
      _ = subst (fun x => liftSub tau (wk x)) (sigma j) := by
            simpa using subst_rename
              (sigma := liftSub tau) (rho := wk) (term := sigma j)
      _ = subst (fun x => rename wk (tau x)) (sigma j) := by rfl
      _ = rename wk (subst tau (sigma j)) := by
            symm
            simpa using rename_subst
              (rho := wk) (sigma := tau) (term := sigma j)
      _ = liftSub (fun x => subst tau (sigma x)) j.succ := by rfl

@[simp] theorem subst_comp :
    ∀ {n m k} (tau : Sub Head m k) (sigma : Sub Head n m)
      (term : Tm Head n),
      subst tau (subst sigma term) =
        subst (fun i => subst tau (sigma i)) term := by
  intro n m k tau sigma term
  induction term generalizing m k tau with
  | var i => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain (tau := tau) (sigma := sigma)]
      calc
        subst (liftSub tau) (subst (liftSub sigma) codomain) =
            subst (fun i => subst (liftSub tau) (liftSub sigma i)) codomain := by
              simpa using ihCodomain
                (tau := liftSub tau) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => subst tau (sigma i))) codomain := by
              apply subst_ext
              intro i
              exact liftSub_comp_apply tau sigma i
  | sigma domain codomain ihDomain ihCodomain =>
      simp [subst, ihDomain (tau := tau) (sigma := sigma)]
      calc
        subst (liftSub tau) (subst (liftSub sigma) codomain) =
            subst (fun i => subst (liftSub tau) (liftSub sigma i)) codomain := by
              simpa using ihCodomain
                (tau := liftSub tau) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => subst tau (sigma i))) codomain := by
              apply subst_ext
              intro i
              exact liftSub_comp_apply tau sigma i
  | id type left right ihType ihLeft ihRight =>
      simp [subst, ihType (tau := tau) (sigma := sigma),
        ihLeft (tau := tau) (sigma := sigma),
        ihRight (tau := tau) (sigma := sigma)]
  | lam body ih =>
      simp [subst]
      calc
        subst (liftSub tau) (subst (liftSub sigma) body) =
            subst (fun i => subst (liftSub tau) (liftSub sigma i)) body := by
              simpa using ih (tau := liftSub tau) (sigma := liftSub sigma)
        _ = subst (liftSub (fun i => subst tau (sigma i))) body := by
              apply subst_ext
              intro i
              exact liftSub_comp_apply tau sigma i
  | app function argument ihFunction ihArgument =>
      simp [subst, ihFunction (tau := tau) (sigma := sigma),
        ihArgument (tau := tau) (sigma := sigma)]
  | pair first second ihFirst ihSecond =>
      simp [subst, ihFirst (tau := tau) (sigma := sigma),
        ihSecond (tau := tau) (sigma := sigma)]
  | fst pair ih => simpa [subst] using ih (tau := tau) (sigma := sigma)
  | snd pair ih => simpa [subst] using ih (tau := tau) (sigma := sigma)
  | refl term ih => simpa [subst] using ih (tau := tau) (sigma := sigma)

/-- Opening a term weakened across the newest binder returns the original
term.  This is the key beta-side cancellation used by nondependent arrows. -/
@[simp] theorem inst0_rename_wk (argument : Tm Head n) (term : Tm Head n) :
    inst0 argument (rename wk term) = term := by
  calc
    inst0 argument (rename wk term) =
        subst (fun i => subst0 argument (wk i)) term := by
          simpa [inst0] using subst_rename
            (sigma := subst0 argument) (rho := wk) (term := term)
    _ = subst ids term := by
          apply subst_ext
          intro i
          rfl
    _ = term := subst_ids term

/-- A codomain authored over one closed parameter may be lifted below an
arbitrary ambient telescope and then opened there.  Opening cancels the
administrative lift and leaves the authored parameter instantiated by the
ambient argument. -/
@[simp] theorem inst0_rename_liftRen_elim0
    (argument : Tm Head n) (body : Tm Head 1) :
    inst0 argument
        (rename (liftRen (Fin.elim0 : Ren 0 n)) body) =
      subst (fun _ : Fin 1 => argument) body := by
  unfold inst0
  rw [subst_rename]
  apply subst_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro impossible
    exact Fin.elim0 impossible

/-- Changing universe heads preserves the use of a closed declaration type
in an arbitrary local telescope. -/
@[simp] theorem Tm.mapHead_liftClosed (map : HeadOne → HeadTwo)
    (term : Tm HeadOne 0) :
    (liftClosed term : Tm HeadOne n).mapHead map =
      liftClosed (term.mapHead map) := by
  simpa only [liftClosed] using
    (Tm.mapHead_rename map Fin.elim0 term)

/-! ## Transport between presentations -/

/-- A constructor-by-constructor morphism between rule packages.  This is the
data needed to transport conversion and typing along a universe-head map. -/
structure Rules.Morphism (source : Rules HeadOne) (target : Rules HeadTwo)
    (map : HeadOne → HeadTwo) where
  headTyping : ∀ {head universeHead}, source.headTyping head universeHead →
    target.headTyping (map head) (map universeHead)
  isUniverse : ∀ {head}, source.isUniverse head → target.isUniverse (map head)
  join : ∀ {left right result}, source.join left right result →
    target.join (map left) (map right) (map result)
  cumulative : ∀ {lower upper}, source.cumulative lower upper →
    target.cumulative (map lower) (map upper)
  headEq : ∀ {left right}, source.headEq left right →
    target.headEq (map left) (map right)
  constantType : ∀ {name type}, source.constantType name = some type →
    target.constantType name = some (type.mapHead map)
  computation : ∀ {n} {left right : Tm HeadOne n},
    source.computation.step left right →
      target.computation.step (left.mapHead map) (right.mapHead map)

/-- A computation/equality generator transports along a head relation map. -/
theorem StepCore.mapHead {sourceEq : HeadOne → HeadOne → Prop}
    {targetEq : HeadTwo → HeadTwo → Prop}
    {sourceRoot : RootComputation HeadOne}
    {targetRoot : RootComputation HeadTwo}
    (map : HeadOne → HeadTwo)
    (mapEq : ∀ {left right}, sourceEq left right →
      targetEq (map left) (map right))
    (mapRoot : ∀ {n} {left right : Tm HeadOne n},
      sourceRoot.step left right →
        targetRoot.step (left.mapHead map) (right.mapHead map))
    {left right : Tm HeadOne n} (step : Step sourceEq left right sourceRoot) :
    Step targetEq (left.mapHead map) (right.mapHead map) targetRoot := by
  induction step with
  | betaPi body argument =>
      simpa only [Tm.mapHead, Tm.mapHead_inst0] using
        (Step.betaPi (headEq := targetEq)
          (body.mapHead map) (argument.mapHead map))
  | betaSigmaFst first second => exact .betaSigmaFst _ _
  | betaSigmaSnd first second => exact .betaSigmaSnd _ _
  | head equality => exact .head (mapEq equality)
  | root computation => exact .root (mapRoot computation)
  | congPiDom step ih => exact .congPiDom ih
  | congPiCod step ih => exact .congPiCod ih
  | congSigmaDom step ih => exact .congSigmaDom ih
  | congSigmaCod step ih => exact .congSigmaCod ih
  | congIdTy step ih => exact .congIdTy ih
  | congIdLeft step ih => exact .congIdLeft ih
  | congIdRight step ih => exact .congIdRight ih
  | congLam step ih => exact .congLam ih
  | congAppFun step ih => exact .congAppFun ih
  | congAppArg step ih => exact .congAppArg ih
  | congPairFst step ih => exact .congPairFst ih
  | congPairSnd step ih => exact .congPairSnd ih
  | congFst step ih => exact .congFst ih
  | congSnd step ih => exact .congSnd ih
  | congRefl step ih => exact .congRefl ih

/-- Conversion transports along a head relation map. -/
theorem Conv.mapHead {sourceEq : HeadOne → HeadOne → Prop}
    {targetEq : HeadTwo → HeadTwo → Prop}
    {sourceRoot : RootComputation HeadOne}
    {targetRoot : RootComputation HeadTwo}
    (map : HeadOne → HeadTwo)
    (mapEq : ∀ {left right}, sourceEq left right →
      targetEq (map left) (map right))
    (mapRoot : ∀ {n} {left right : Tm HeadOne n},
      sourceRoot.step left right →
        targetRoot.step (left.mapHead map) (right.mapHead map))
    {left right : Tm HeadOne n}
    (conversion : Conv sourceEq left right sourceRoot) :
    Conv targetEq (left.mapHead map) (right.mapHead map) targetRoot := by
  induction conversion with
  | rel left right step => exact .rel _ _ (step.mapHead map mapEq mapRoot)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

/-- Typing transports along any constructor-preserving rule morphism. -/
theorem HasType.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {Gamma : Ctx HeadOne n} {term type : Tm HeadOne n}
    (typing : HasType source Gamma term type) :
    HasType target (Gamma.mapHead map) (term.mapHead map) (type.mapHead map) := by
  induction typing with
  | headType headTyping => exact .headType (morphism.headTyping headTyping)
  | @var n Gamma i =>
      simpa only [Tm.mapHead, Ctx.lookup_mapHead] using
        (HasType.var (R := target) (Γ := Gamma.mapHead map) i)
  | @const n Gamma name type constantTyping =>
      simpa only [Tm.mapHead, Tm.mapHead_liftClosed] using
        (HasType.const (R := target) (Γ := Gamma.mapHead map)
          (morphism.constantType constantTyping))
  | piForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      exact .piForm ihType (morphism.isUniverse typeUniverse)
        ihBody (morphism.isUniverse bodyUniverse) (morphism.join join)
  | sigmaForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      exact .sigmaForm ihType (morphism.isUniverse typeUniverse)
        ihBody (morphism.isUniverse bodyUniverse) (morphism.join join)
  | lamIntro bodyTyping ihBody => exact .lamIntro ihBody
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      simpa only [Tm.mapHead, Tm.mapHead_inst0] using
        (HasType.appElim ihFunction ihArgument)
  | pairIntro firstTyping secondTyping ihFirst ihSecond =>
      have ihSecond' := ihSecond
      rw [Tm.mapHead_inst0] at ihSecond'
      exact .pairIntro ihFirst ihSecond'
  | fstElim pairTyping ihPair => exact .fstElim ihPair
  | sndElim pairTyping ihPair =>
      simpa only [Tm.mapHead, Tm.mapHead_inst0] using
        (HasType.sndElim ihPair)
  | idForm typeTyping universeWitness leftTyping rightTyping
      ihType ihLeft ihRight =>
      exact .idForm ihType (morphism.isUniverse universeWitness) ihLeft ihRight
  | reflIntro termTyping ihTerm => exact .reflIntro ihTerm
  | cumul prior order ihPrior =>
      exact .cumul ihPrior (morphism.cumulative order)
  | conv prior conversion ihPrior =>
      exact .conv ihPrior
        (conversion.mapHead map morphism.headEq morphism.computation)

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
