/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

-- these definitions and theorems should be moved to the HoTT library

import types.nat
open eq nat
namespace my
variables {A A' : Type} {B B' : A → Type} {C : Π⦃a⦄, B a → Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

  definition cast_apo011 {P : Πa, B a → Type} {Ha : a = a₂} (Hb : b =[Ha] b₂) (p : P a b) :
    cast (apo011 P Ha Hb) p = Hb ▸o p :=
  by induction Hb; reflexivity

  definition fn_tro_eq_tro_fn {C' : Π ⦃a : A⦄, B a → Type} (q : b =[p] b₂)
    (f : Π⦃a : A⦄ (b : B a), C b → C' b) (c : C b) : f b₂ (q ▸o c) = (q ▸o (f b c)) :=
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

--not used

  definition pathover_ap_invo {B' : A' → Type} (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂)
    : pathover_ap B' f q⁻¹ᵒ =[ap_inv f p] (pathover_ap B' f q)⁻¹ᵒ :=
  by induction q; exact idpo

  definition add_add (n l k : ℕ) : n + l + k = n + (k + l) :=
  begin
    induction l with l IH,
      reflexivity,
      exact succ_add (n + l) k ⬝ ap succ IH
  end

  definition add.comm (n m : ℕ) : n + m = m + n :=
  begin
    induction n with n IH,
    { apply zero_add},
    { exact !succ_add ⬝ ap succ IH}
  end

  definition apo011_inv (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : (apo011 f Ha Hb)⁻¹ = (apo011 f Ha⁻¹ Hb⁻¹ᵒ) :=
  by induction Hb; reflexivity


end my
