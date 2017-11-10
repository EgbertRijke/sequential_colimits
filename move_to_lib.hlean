/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

-- these definitions and theorems should be moved to the HoTT library

import types.equiv cubical.pathover2 eq2 types.eq types.fin types.pointed2
open eq nat algebra is_equiv equiv function sigma is_trunc fin

attribute tro_invo_tro [unfold 9] -- TODO: move

  /- replace proof of le_of_succ_le by this -/
  definition le_step_left {n m : ℕ} (H : succ n ≤ m) : n ≤ m :=
  by induction H with H m H'; exact le_succ n; exact le.step H'

  /- TODO: make proof of le_succ_of_le simpler -/

  definition nat.add_le_add_left2 {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
  by induction H with m H H₂; reflexivity; exact le.step H₂

  -- definition le_add_right2 (n k : ℕ) : n ≤ n + k :=
  -- by induction H with m H H₂

  -- example : le_add_right 0 = (λn, nat.zero_le (0+n)) :=
  -- idp

/- move this to types.eq -/
definition total_space_method2 {A : Type} (a₀ : A) (code : A → Type) (H : is_contr (Σa, code a))
  (c₀ : code a₀) (a : A) : (a₀ = a) ≃ code a :=
total_space_method a₀ code H (ap pr1 (center_eq ⟨a₀, c₀⟩)) a

definition total_space_method2_refl {A : Type} (a₀ : A) (code : A → Type) (H : is_contr (Σa, code a))
  (c₀ : code a₀) : total_space_method2 a₀ code H c₀ a₀ idp = c₀ :=
begin
   exact sorry --esimp [total_space_method2, total_space_method, eq.encode],
end

definition equiv_pathover2 {A : Type} {a a' : A} (p : a = a')
  {B : A → Type} {C : A → Type} (f : B a ≃ C a) (g : B a' ≃ C a')
  (r : to_fun f =[p] to_fun g) : f =[p] g :=
begin
  fapply pathover_of_fn_pathover_fn,
  { intro a, apply equiv.sigma_char },
  { apply sigma_pathover _ _ _ r, apply is_prop.elimo }
end

definition equiv_pathover_inv {A : Type} {a a' : A} (p : a = a')
  {B : A → Type} {C : A → Type} (f : B a ≃ C a) (g : B a' ≃ C a')
  (r : to_inv f =[p] to_inv g) : f =[p] g :=
begin
  /- this proof is a bit weird, but it works -/
  apply equiv_pathover2,
  change f⁻¹ᶠ⁻¹ᶠ =[p] g⁻¹ᶠ⁻¹ᶠ,
  apply apo (λ(a: A) (h : C a ≃ B a), h⁻¹ᶠ),
  apply equiv_pathover2,
  exact r
end

definition transport_lemma {A : Type} {C : A → Type} {g₁ : A → A}
  {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
  transport C (ap g₁ p)⁻¹ (f (transport C p z)) = f z :=
by induction p; reflexivity

definition transport_lemma2 {A : Type} {C : A → Type} {g₁ : A → A}
  {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
  transport C (ap g₁ p) (f z) = f (transport C p z) :=
by induction p; reflexivity

definition iterate_equiv2 {A : Type} {C : A → Type} (f : A → A) (h : Πa, C a ≃ C (f a))
  (k : ℕ) (a : A) : C a ≃ C (f^[k] a) :=
begin induction k with k IH, reflexivity, exact IH ⬝e h (f^[k] a) end

definition ap_sigma_functor_sigma_eq {A A' : Type} {B : A → Type} {B' : A' → Type}
  {a a' : A} {b : B a} {b' : B a'} (f : A → A') (g : Πa, B a → B' (f a)) (p : a = a') (q : b =[p] b') :
  ap (sigma_functor f g) (sigma_eq p q) = sigma_eq (ap f p) (pathover_ap B' f (apo g q)) :=
by induction q; reflexivity

definition ap_sigma_functor_id_sigma_eq {A : Type} {B B' : A → Type}
  {a a' : A} {b : B a} {b' : B a'} (g : Πa, B a → B' a) (p : a = a') (q : b =[p] b') :
  ap (sigma_functor id g) (sigma_eq p q) = sigma_eq p (apo g q) :=
by induction q; reflexivity

definition sigma_eq_pr2_constant {A B : Type} {a a' : A} {b b' : B} (p : a = a')
  (q : b =[p] b') : ap pr2 (sigma_eq p q) = (eq_of_pathover q) :=
by induction q; reflexivity

definition sigma_eq_pr2_constant2 {A B : Type} {a a' : A} {b b' : B} (p : a = a')
  (q : b = b') : ap pr2 (sigma_eq p (pathover_of_eq p q)) = q :=
by induction p; induction q; reflexivity

definition sigma_eq_concato_eq {A : Type} {B : A → Type} {a a' : A} {b : B a} {b₁ b₂ : B a'}
  (p : a = a') (q : b =[p] b₁) (q' : b₁ = b₂) : sigma_eq p (q ⬝op q') = sigma_eq p q ⬝ ap (dpair a') q' :=
by induction q'; reflexivity

definition eq_of_pathover_apo {A C : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'}
  {p : a = a'} (g : Πa, B a → C) (q : b =[p] b') :
  eq_of_pathover (apo g q) = apd011 g p q :=
by induction q; reflexivity

definition lift_succ2 [constructor] ⦃n : ℕ⦄ (x : fin n) : fin (succ n) :=
fin.mk x (le.step (is_lt x))

open fiber pointed
definition fiber_functor [constructor] {A A' B B' : Type} {f : A → B} {f' : A' → B'} {b : B} {b' : B'}
  (g : A → A') (h : B → B') (H : hsquare g h f f') (p : h b = b') (x : fiber f b) : fiber f' b' :=
fiber.mk (g (point x)) (H (point x) ⬝ ap h (point_eq x) ⬝ p)

definition pfiber_functor [constructor] {A A' B B' : Type*} {f : A →* B} {f' : A' →* B'}
  (g : A →* A') (h : B →* B') (H : psquare g h f f') : pfiber f →* pfiber f' :=
pmap.mk (fiber_functor g h H (respect_pt h))
  begin
    fapply fiber_eq,
      exact respect_pt g,
      exact !con.assoc ⬝ to_homotopy_pt H
  end
