/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import types.nat .move_to_lib types.fin types.trunc

open nat eq equiv sigma sigma.ops is_equiv is_trunc trunc

  definition id_rec : ℕ → ℕ :=
  nat.rec 0 (λn m, succ m)

  -- MOVE
  definition idontwanttoprovethis (n l k : ℕ) :
    succ_add (n + l) k ⬝ nat.add_assoc n l (succ k) ⬝ ap
    (λ z, n + z)
    (succ_add l k)⁻¹ = nat.add_assoc n (succ l) k :=
  begin
    induction k with k IH,
    { reflexivity},
    { esimp, refine _ ⬝ ap02 succ IH,
      apply is_prop.elim }
  end

  /- replace proof of le_of_succ_le by this -/
  definition le_step_left {n m : ℕ} (H : succ n ≤ m) : n ≤ m :=
  by induction H with H m H'; exact le_succ n; exact le.step H'

  /- TODO: make proof of le_succ_of_le simpler -/

  definition nat.add_le_add_left2 {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
  by induction H with m H H₂; reflexivity; exact le.step H₂

namespace seq_colim

  definition seq_diagram [reducible] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  definition is_equiseq [reducible] {A : ℕ → Type} (f : seq_diagram A) : Type :=
  forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type :=
    (carrier : ℕ → Type)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [coercion]

  variables {A : ℕ → Type} (f : seq_diagram A)
  include f

  definition lrep {n m : ℕ} (H : n ≤ m) (x : A n) : A m :=
  begin
    induction H with m H y,
    { exact x },
    { exact f y }
  end

  definition lrep_irrel {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (p : m = m') (x : A n) :
    lrep f H₁ x =[p] lrep f H₂ x :=
  apo (λm H, lrep f H x) !is_prop.elimo

  definition lrep_irrel_eq {n m : ℕ} (H₁ H₂ : n ≤ m) (x : A n) : lrep f H₁ x = lrep f H₂ x :=
  ap (λH, lrep f H x) !is_prop.elim

  definition lrep_irrel_eq2 {n m : ℕ} (H₁ H₂ : n ≤ m) (x : A n) :
    lrep_irrel_eq f (le.step H₁) (le.step H₂) x = ap (@f m) (lrep_irrel_eq f H₁ H₂ x) :=
  begin
    have H₁ = H₂, from !is_prop.elim, induction this,
    refine ap02 _ !is_prop_elim_self ⬝ _ ⬝ ap02 _(ap02 _ !is_prop_elim_self⁻¹),
    reflexivity
  end

  definition lrep_eq_lrep_irrel {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (x y : A n) (p : m = m') :
    (lrep f H₁ x = lrep f H₁ y) ≃ (lrep f H₂ x = lrep f H₂ y) :=
  equiv_apd011 (λm H, lrep f H x = lrep f H y) (is_prop.elimo p H₁ H₂)

  definition lrep_eq_lrep_irrel_natural {n m m' : ℕ} {H₁ : n ≤ m} (H₂ : n ≤ m') {x y : A n}
    (p : m = m') (q : lrep f H₁ x = lrep f H₁ y) :
    lrep_eq_lrep_irrel f (le.step H₁) (le.step H₂) x y (ap succ p) (ap (@f m) q) =
    ap (@f m') (lrep_eq_lrep_irrel f H₁ H₂ x y p q) :=
  begin
    esimp [lrep_eq_lrep_irrel],
    symmetry,
    refine fn_tro_eq_tro_fn2 _ (λx y, ap (@f _)) q ⬝ _,
    refine ap (λx, x ▸o _) (@is_prop.elim _ _ _ _),
    apply is_trunc_pathover
  end

  definition is_equiv_lrep [constructor] [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) :
    is_equiv (lrep f H) :=
  begin
    induction H with m H Hlrepf,
    { apply is_equiv_id },
    { exact is_equiv_compose (@f _) (lrep f H) },
  end

  local attribute is_equiv_lrep [instance]
  definition lrep_back [reducible] [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) : A m → A n :=
  (lrep f H)⁻¹ᶠ

  section generalized_lrep
  variable {n : ℕ}

  -- definition lrep_pathover_lrep0 [reducible] (k : ℕ) (a : A 0) : lrep f k a =[nat.zero_add k] lrep0 f k a :=
  -- begin induction k with k p, constructor, exact pathover_ap A succ (apo f p) end

  /- lreplace le_of_succ_le with this -/

  definition lrep_f {n m : ℕ} (H : succ n ≤ m) (a : A n) :
    lrep f H (f a) = lrep f (le_step_left H) a :=
  begin
    induction H with m H p,
    { reflexivity },
    { exact ap (@f m) p }
  end

  definition lrep_lrep {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) (a : A n) :
    lrep f H2 (lrep f H1 a) = lrep f (nat.le_trans H1 H2) a :=
  begin
    induction H2 with k H2 p,
    { reflexivity },
    { exact ap (@f k) p }
  end

  -- -- this should be a squareover
  -- definition lrep_lrep_succ (k l : ℕ) (a : A n) :
  --   lrep_lrep f k (succ l) a = change_path (idontwanttoprovethis n l k)
  --   (lrep_f f k (lrep f l a) ⬝o
  --    lrep_lrep f (succ k) l a ⬝o
  --    pathover_ap _ (λz, n + z) (apd (λz, lrep f z a) (succ_add l k)⁻¹ᵖ)) :=
  -- begin
  --   induction k with k IH,
  --   { constructor},
  --   { exact sorry}
  -- end

  definition f_lrep {n m : ℕ} (H : n ≤ m) (a : A n) : f (lrep f H a) = lrep f (le.step H) a := idp

  definition rep (m : ℕ) (x : A n) : A (n + m) :=
  lrep f (le_add_right n m) x

  definition old_rep (m : ℕ) (x : A n) : A (n + m) :=
  by induction m with m y; exact x; exact f y

  definition rep_eq_old_rep (m : ℕ) (x : A n) : rep f m x = old_rep f m x :=
  by induction m with m p; reflexivity; exact ap (@f _) p

  definition rep_f (k : ℕ) (a : A n) :
    pathover A (rep f k (f a)) (succ_add n k) (rep f (succ k) a) :=
  begin
    induction k with k IH,
    { constructor },
    { unfold [succ_add], apply pathover_ap, exact apo f IH}
  end

  definition rep_rep (k l : ℕ) (a : A n) :
    pathover A (rep f k (rep f l a)) (nat.add_assoc n l k) (rep f (l + k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  end generalized_lrep

  section shift

  definition shift_diag [unfold_full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [unfold_full] (k : ℕ) : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [unfold_full] (k : ℕ) : seq_diagram (λn, A (n + k)) :=
  λn a, transport A (succ_add n k)⁻¹ (f a)

  definition lrep_kshift_diag {n m k : ℕ} (H : m ≤ k) (x : A (n + m)) :
    lrep (kshift_diag f n) H x = lrep f (nat.add_le_add_left2 H n) x :=
  by induction H with k H p; reflexivity; exact ap (@f _) p

  end shift

  section constructions

    omit f

    definition constant_seq (X : Type) : seq_diagram (λ n, X) :=
    λ n x, x

    definition seq_diagram_arrow_left [unfold_full] (X : Type) : seq_diagram (λn, X → A n) :=
    λn g x, f (g x)

    definition seq_diagram_fin : seq_diagram fin :=
    λn, fin.lift_succ

    definition id0_seq [unfold_full] (x y : A 0) : ℕ → Type :=
    λ k, lrep f (zero_le k) x = lrep f (zero_le k) y

    definition id0_seq_diagram [unfold_full] (x y : A 0) : seq_diagram (id0_seq f x y) :=
    λ (k : ℕ) (p : lrep f (zero_le k) x = lrep f (zero_le k) y), ap (@f k) p

    definition id_seq [unfold_full] (n : ℕ) (x y : A n) : ℕ → Type :=
    λ k, rep f k x = rep f k y

    definition id_seq_diagram [unfold_full] (n : ℕ) (x y : A n) : seq_diagram (id_seq f n x y) :=
    λ (k : ℕ) (p : rep f k x = rep f k y), ap (@f (n + k)) p

    definition trunc_diagram [unfold_full] (k : ℕ₋₂) (f : seq_diagram A) :
      seq_diagram (λn, trunc k (A n)) :=
    λn, trunc_functor k (@f n)

  end constructions

  section over

    variable {A}
    variable (P : Π⦃n⦄, A n → Type)

    definition seq_diagram_over : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

    variable (g : seq_diagram_over f P)
    variables {f P}

    definition seq_diagram_of_over [unfold_full] {n : ℕ} (a : A n) :
      seq_diagram (λk, P (lrep f (le_add_right n k) a)) :=
    λk p, g p

    definition seq_diagram_sigma [unfold 6] : seq_diagram (λn, Σ(x : A n), P x) :=
    λn v, ⟨f v.1, g v.2⟩

    variables {n : ℕ} (f P)

    theorem rep_f_equiv [constructor] (a : A n) (k : ℕ) :
      P (lrep f (le_add_right (succ n) k) (f a)) ≃ P (lrep f (le_add_right n (succ k)) a) :=
    equiv_apd011 P (rep_f f k a)

    theorem rep_rep_equiv [constructor] (a : A n) (k l : ℕ) :
      P (rep f (l + k) a) ≃ P (rep f k (rep f l a)) :=
    (equiv_apd011 P (rep_rep f k l a))⁻¹ᵉ

  end over

  omit f
  -- do we need to generalize this to the case where the bottom sequence consists of equivalences?
  definition seq_diagram_pi {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n)) :
    seq_diagram (λn, Πx, A x n) :=
  λn f x, g (f x)

end seq_colim
