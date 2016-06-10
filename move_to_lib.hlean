/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

-- these definitions and theorems should be moved to the HoTT library

import types.nat
open eq nat algebra is_equiv equiv function
namespace my
variables {A A' : Type} {B B' : A → Type} {C : Π⦃a⦄, B a → Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

  definition cast_apo011 {P : Πa, B a → Type} {Ha : a = a₂} (Hb : b =[Ha] b₂) (p : P a b) :
    cast (apo011 P Ha Hb) p = Hb ▸o p :=
  by induction Hb; reflexivity

  -- this replaces the definition in init.pathover?
  definition fn_tro_eq_tro_fn {C' : Π ⦃a : A⦄, B a → Type} (q : b =[p] b₂)
    (f : Π⦃a : A⦄ (b : B a), C b → C' b) (c : C b) : f b₂ (q ▸o c) = q ▸o (f b c) :=
  by induction q;reflexivity

  -- TODO: prove for generalized apo
  definition apo_tro (C : Π⦃a⦄, B' a → Type) (f : Π⦃a⦄, B a → B' a) (q : b =[p] b₂)
    (c : C (f b)) : apo f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b) : pathover_ap B' f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_invo_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b₂)
    : (pathover_ap B' f q)⁻¹ᵒ ▸o c = q⁻¹ᵒ ▸o c :=
  by induction q; reflexivity

  -- TODO: prove for generalized apo
  definition apo_invo (f : Πa, B a → B' a) {Ha : a = a₂} (Hb : b =[Ha] b₂)
      : (apo f Hb)⁻¹ᵒ = apo f Hb⁻¹ᵒ :=
  by induction Hb; reflexivity

  definition pathover_tro {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b) :
    c =[apo011 C p q] q ▸o c :=
  by induction q; constructor

  definition pathover_ap_invo {B' : A' → Type} (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂)
    : pathover_ap B' f q⁻¹ᵒ =[ap_inv f p] (pathover_ap B' f q)⁻¹ᵒ :=
  by induction q; exact idpo

  definition apo011_inv (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : (apo011 f Ha Hb)⁻¹ = (apo011 f Ha⁻¹ Hb⁻¹ᵒ) :=
  by induction Hb; reflexivity

  definition tro_invo_tro [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b') :
    q ▸o (q⁻¹ᵒ ▸o c) = c :=
  by induction q; reflexivity

  definition invo_tro_tro [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b) :
    q⁻¹ᵒ ▸o (q ▸o c) = c :=
  by induction q; reflexivity

  definition cono_tro [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a₁ a₂ a₃ : A} {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) (c : C b₁) :
    transporto C (q₁ ⬝o q₂) c = transporto C q₂ (transporto C q₁ c) :=
  by induction q₂; reflexivity

  definition is_equiv_transporto [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : is_equiv (transporto C q) :=
  begin
    fapply adjointify,
    { exact transporto C q⁻¹ᵒ},
    { exact tro_invo_tro C q},
    { exact invo_tro_tro C q}
  end

  -- rename to apd011_equiv? also rename apo011 -> apd011 and maybe ap_equiv -> equiv_ap
  definition equiv_apd011 [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : C b ≃ C b' :=
  equiv.mk (transporto C q) !is_equiv_transporto

  -- MOVE:
  attribute apo0111 [unfold 12 13 14]
  attribute elim_inv_inv [unfold 5]
  attribute eq.inv_inv [unfold 4]
  attribute idp_rec_on [unfold 7]
  attribute adjointify_left_inv' [unfold_full]
  -- reorder arguments to make consistent with natural_square
  definition natural_square011 {A A' : Type} {B : A → Type}
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b')
    {l r  : Π⦃a⦄, B a → A'} (g : Π⦃a⦄ (b : B a), l b = r b)
    : square (apo011 l p q) (apo011 r p q) (g b) (g b') :=
  begin
    induction q, exact hrfl
  end

  definition natural_square0111' {A A' : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
    {c : C b} {c' : C b'} (s : c =[apo011 C p q] c')
    {l r  : Π⦃a⦄ {b : B a}, C b → A'}
    (g : Π⦃a⦄ {b : B a} (c : C b), l c = r c)
    : square (apo0111 l p q s) (apo0111 r p q s) (g c) (g c') :=
  begin
    induction q, esimp at s, induction s using idp_rec_on, exact hrfl
  end

  -- this can be generalized a bit, by making the domain and codomain of k different, and also have
  -- a function at the RHS of s (similar to m)
  definition natural_square0111 {A A' : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
    {c : C b} {c' : C b'} (r : c =[apo011 C p q] c')
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    {f  : Π⦃a⦄ {b : B a}, C b → A'}
    (s : Π⦃a⦄ {b : B a} (c : C b), f (m c) = f c)
    : square (apo0111 (λa b c, f (m c)) p q r) (apo0111 f p q r) (s c) (s c') :=
  begin
    induction q, esimp at r, induction r using idp_rec_on, exact hrfl
  end

  definition apdo011 {A : Type} {B : A → Type} {C : Π⦃a⦄, B a → Type}
    (f : Π⦃a⦄ (b : B a), C b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
      : f b =[apo011 C p q] f b' :=
  by cases q; constructor

  definition apdo0111 {A : Type} {B : A → Type} {C C' : Π⦃a⦄, B a → Type}
    (f : Π⦃a⦄ {b : B a}, C b → C' b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
    {c : C b} {c' : C b'} (r : c =[apo011 C p q] c')
      : f c =[apo011 C' p q] f c' :=
  begin
    induction q, esimp at r, induction r using idp_rec_on, constructor
  end

  definition fn_tro_eq_tro_fn2 (q : b =[p] b₂)
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    (c : C b) :
    m (q ▸o c) = (pathover_ap B k (apo l q)) ▸o (m c) :=
  by induction q; reflexivity

  definition apo0111_precompose {A A' : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    (f  : Π⦃a⦄ {b : B a}, C b → A')
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
    (c : C b)
    : apo0111 (λa b c, f (m c)) p q (pathover_tro C q c) ⬝ ap (@f _ _) (fn_tro_eq_tro_fn2 q m c) =
      apo0111 f (ap k p) (pathover_ap B k (apo l q)) (my.pathover_tro C _ (m c)) :=
  by induction q; reflexivity

end my

export [unfold] my
