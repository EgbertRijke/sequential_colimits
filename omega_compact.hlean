/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import .seq_colim

open eq nat is_equiv equiv is_trunc pi unit function

  section funext
  open funext

  variables {A B C : Type} {g g' : B → C} {f f' : A → B} {P : A → Type}

  definition hwhisker_left [unfold_full] (g : B → C) {f f' : A → B} (H : f ~ f') :
    g ∘ f ~ g ∘ f' :=
  λa, ap g (H a)

  definition hwhisker_right [unfold_full] (f : A → B) (H : g ~ g') :
    g ∘ f ~ g' ∘ f :=
  λa, H (f a)

  protected definition homotopy.rec_on' {f f' : Πa, P a} {Q : (f ~ f') → (f = f') → Type}
    (p : f ~ f') (H : Π(q : f = f'), Q (apd10 q) q) : Q p (eq_of_homotopy p) :=
  begin
    refine homotopy.rec_on p _,
    intro q, exact (left_inv (apd10) q)⁻¹ ▸ H q
  end

  protected definition homotopy.rec_on_idp' {f : Πa, P a} {Q : Π{g}, (f ~ g) → (f = g) → Type}
    {g : Πa, P a} (p : f ~ g) (H : Q (homotopy.refl f) idp) : Q p (eq_of_homotopy p) :=
  begin
    refine homotopy.rec_on' p _, intro q, induction q, exact H
  end

  definition compose_eq_of_homotopy {A B C : Type} (g : B → C) {f f' : A → B} (H : f ~ f') :
    ap (λf, g ∘ f) (eq_of_homotopy H) = eq_of_homotopy (hwhisker_left g H) :=
  begin
    refine homotopy.rec_on_idp' H _, exact !eq_of_homotopy_idp⁻¹
  end

  definition unit_arrow_eq {X : Type} (f : unit → X) : (λx, f ⋆) = f :=
  by apply eq_of_homotopy; intro u; induction u; reflexivity

  definition unit_arrow_eq_compose {X Y : Type} (g : X → Y) (f : unit → X) :
    unit_arrow_eq (g ∘ f) = ap (λf, g ∘ f) (unit_arrow_eq f) :=
  begin
    apply eq_of_fn_eq_fn' apd10,
    refine right_inv apd10 _ ⬝ _,
    refine _ ⬝ ap apd10 (!compose_eq_of_homotopy)⁻¹,
    refine _ ⬝ (right_inv apd10 _)⁻¹,
    apply eq_of_homotopy, intro u, induction u, reflexivity
  end

  end funext


namespace seq_colim

  variables {A : ℕ → Type} (f : seq_diagram A)
  variables {n : ℕ} (a : A n)

  definition arrow_colim_of_colim_arrow [unfold 4] {X : Type}
    (g : seq_colim (seq_diagram_arrow_left f X)) (x : X) : seq_colim f :=
  begin induction g with n g n g, exact ι f (g x), exact glue f (g x) end

  definition omega_compact [class] (X : Type) : Type :=
  Π(A : ℕ → Type) (f : seq_diagram A),
  is_equiv (arrow_colim_of_colim_arrow f :
             seq_colim (seq_diagram_arrow_left f X) → (X → seq_colim f))

  local attribute is_contr_seq_colim [instance]
  definition is_contr_empty_arrow [instance] (X : Type) : is_contr (empty → X) :=
  by apply is_trunc_pi; contradiction

  definition omega_compact_empty [instance] [constructor] : omega_compact empty :=
  begin
    intro A f,
    fapply adjointify,
    { intro g, exact ι' _ 0 empty.elim},
    { intro g, apply eq_of_homotopy, contradiction},
    { intro h, apply is_prop.elim}
  end

  definition omega_compact_unit [instance] [constructor] : omega_compact unit :=
  begin
    intro A f,
    fapply adjointify,
    { intro g, induction g ⋆,
      { exact ι _ (λx, a)},
      { apply glue}},
    { intro g, apply eq_of_homotopy, intro u, induction u,
      induction g ⋆,
      { reflexivity},
      { esimp, apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose (λx, arrow_colim_of_colim_arrow f x ⋆) _ _ ⬝ _,
        refine ap02 _ !elim_glue ⬝ _, apply elim_glue}},
    { intro h, induction h with n h n h,
      { esimp, apply ap (ι' _ n), apply unit_arrow_eq},
      { esimp, apply eq_pathover_id_right,
        refine ap_compose' (seq_colim.elim _ _ _) _ _ ⬝ph _,
        refine ap02 _ !elim_glue ⬝ph _,
        refine !elim_glue ⬝ph _,
        refine _ ⬝pv natural_square (@glue _ (seq_diagram_arrow_left f unit) n) (unit_arrow_eq h),
        refine _ ⬝ (ap_compose (ι' _ _) _ _)⁻¹,
        apply ap02, unfold [seq_diagram_arrow_left],
        apply unit_arrow_eq_compose}}
  end

  definition seq_colim_pi_equiv {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n)) :
    seq_colim (seq_diagram_pi g) ≃ Πx, seq_colim (@g x) :=
  begin

  end

  -- The following is a start of a different proof, which proves first that the types are equivalent
  -- definition omega_compact_unit2 [instance] [constructor] : omega_compact unit :=
  -- begin
  --   intro A f,
  --   fapply is_equiv_of_equiv_of_homotopy,
  --   { refine _ ⬝e !arrow_unit_left⁻¹ᵉ, fapply seq_colim_equiv,
  --     { intro n, apply arrow_unit_left},
  --     intro n f, reflexivity},
  --   { esimp, intro x, apply eq_of_homotopy, intro u, induction u, esimp,
  --     induction x with n g n g,
  --     { reflexivity},
  --     apply eq_pathover, apply hdeg_square,
  --     }
  -- end

end seq_colim
