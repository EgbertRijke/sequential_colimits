/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/
import hit.colimit .sequence cubical.squareover types.arrow .move_to_lib types.equiv
       cubical.pathover2 .squareover

open eq nat sigma sigma.ops quotient equiv pi is_trunc is_equiv fiber function

attribute tro_invo_tro [unfold 9] -- TODO: move

--   local attribute is_equiv_compose [reducible]
--   definition right_inv_compose {A B C : Type} (g : B → C) (f : A → B) [is_equiv g] [is_equiv f]
--     /-(H : is_equiv (g ∘ f))-/ (c : C) :
--     @(right_inv (g ∘ f)) !is_equiv_compose c =
--     ap g (right_inv f (g⁻¹ c)) ⬝ right_inv g c :=
-- --ap g (right_inv f (g⁻¹ c)) ⬝
--   _
-- -- exit



namespace seq_colim

  -- note: this clashes with the abbreviation defined in namespace "colimit"
  abbreviation ι  [constructor] := @inclusion
  abbreviation ι' [constructor] [parsing_only] {A} (f n) := @inclusion A f n

  variables {A : ℕ → Type} (f : seq_diagram A)

  definition rep0_glue (k : ℕ) (a : A 0) : ι f (rep0 f k a) = ι f a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue f (rep0 f k a) ⬝ IH}
  end

  -- probably not needed
  -- definition rep0_back_glue [is_equiseq f] (k : ℕ) (a : A k) : ι f (rep0_back f k a) = ι f a :=
  -- begin
  --   exact sorry
  -- end

  definition colim_back [unfold 4] [H : is_equiseq f] : seq_colim f → A 0 :=
  begin
    intro x,
    induction x with k a k a,
    { exact rep0_back f k a},
    rexact ap (rep0_back f k) (left_inv (@f k) a),
  end

set_option pp.binder_types true

  definition inv_homotopy_inv_of_homotopy {A B : Type} (f g : A → B) (p : f ~ g)
    [is_equiv f] [is_equiv g] : f⁻¹ ~ g⁻¹ :=
  λa, ap f⁻¹ ((right_inv g a)⁻¹ ⬝ (p (g⁻¹ a))⁻¹) ⬝ left_inv f (g⁻¹ a)

  section
  local attribute is_equiv_rep0 [instance] --[priority 500]
  definition is_equiv_ι (H : is_equiseq f) : is_equiv (ι' f 0) :=
  begin
    fapply adjointify,
    { exact colim_back f},
    { intro x, induction x with k a k a,
      { esimp,
        refine (rep0_glue f k (rep0_back f k a))⁻¹ ⬝ _,
        exact ap (ι f) (right_inv (rep0 f k) a)},
      apply eq_pathover_id_right,
      refine (ap_compose (ι f) (colim_back f) _) ⬝ph _,
      refine ap02 _ _ ⬝ph _, rotate 1,
      { rexact elim_glue f _ _ a},
      refine _ ⬝pv ((natural_square (rep0_glue f k)
                                    (ap (rep0_back f k) (left_inv (@f k) a)))⁻¹ʰ ⬝h _),
      { exact (glue f (rep0 f k (rep0_back f (succ k) (f a))))⁻¹ ⬝
              ap (ι f) (right_inv (rep0 f (succ k)) (f a))},
      { rewrite [-con.assoc, -con_inv]},
      refine !ap_compose⁻¹ ⬝ ap_compose (ι f) _ _ ⬝ph _,
      refine dconcat (aps (ι' f k) (natural_square (right_inv (rep0 f k))
                                                   (left_inv (@f _) a))) _,
      apply move_top_of_left, apply move_left_of_bot,
      refine ap02 _ (whisker_left _ (adj (@f _) a)) ⬝pv _,
      rewrite [-+ap_con, -ap_compose', ap_id],
      apply natural_square_tr},
    intro a,
    reflexivity,
  end
  end

  section
  variables {n : ℕ} (a : A n)

  definition rep_glue (k : ℕ) (a : A n) : ι f (rep f k a) = ι f a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue f (rep f k a) ⬝ IH}
  end

  definition shift_up [unfold 3] (x : seq_colim f) : seq_colim (shift_diag f) :=
  begin
    induction x,
    { exact ι' (shift_diag f) n (f a)},
    { exact glue (shift_diag f) (f a)}
  end

  definition shift_down [unfold 3] (x : seq_colim (shift_diag f)) : seq_colim f :=
  begin
    induction x,
    { exact ι' f (n+1) a},
    { exact glue f a}
  end

  -- definition kshift_up (k : ℕ) (a : seq_colim A) : @seq_colim (λn, A (k + n)) (kshift_diag A k) :=
  -- begin
  --   induction a,
  --   { apply ι' n, refine my.add.comm n k ▸ rep k a},
  --   { exact sorry}
  -- end

  -- definition kshift_down (k : ℕ) (a : @seq_colim (λn, A (k + n)) (kshift_diag A k)) : seq_colim A :=
  -- begin
  --   induction a,
  --   { exact ι a},
  --   { exact glue a}
  -- end

  -- definition kshift_up' (k : ℕ) (x : seq_colim f) : seq_colim (kshift_diag' f k) :=
  -- begin
  --   induction x,
  --   { apply ι' _ n, exact rep f k a},
  --   { exact sorry}
  -- end

  -- definition kshift_down' (k : ℕ) (x : seq_colim (kshift_diag' f k)) : seq_colim f :=
  -- begin
  --   induction x,
  --   { exact ι f a},
  --   { esimp, exact sorry}
  -- end

  end

  variable (A)
  definition shift_equiv [constructor] : seq_colim f ≃ seq_colim (shift_diag f) :=
  equiv.MK (shift_up f)
           (shift_down f)
           abstract begin
             intro x, induction x,
             { exact glue _ a },
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_up f) (shift_down f), ↑shift_down,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹ }
           end end
           abstract begin
             intro x, induction x,
             { exact glue _ a },
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_down f) (shift_up f), ↑shift_up,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹ }
           end end

  -- definition kshift_equiv [constructor] (k : ℕ)
  --   : seq_colim A ≃ @seq_colim (λn, A (k + n)) (kshift_diag A k) :=
  -- equiv.MK (kshift_up k)
  --          (kshift_down k)
  --          abstract begin
  --            intro a, exact sorry,
  --            -- induction a,
  --            -- { esimp, exact glue a},
  --            -- { apply eq_pathover,
  --            --   rewrite [▸*, ap_id, ap_compose shift_up shift_down, ↑shift_down,
  --            --            @elim_glue (λk, A (succ k)) _, ↑shift_up],
  --            --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
  --          end end
  --          abstract begin
  --            intro a, exact sorry
  --            -- induction a,
  --            -- { exact glue a},
  --            -- { apply eq_pathover,
  --            --   rewrite [▸*, ap_id, ap_compose shift_down shift_up, ↑shift_up,
  --            --            @elim_glue A _, ↑shift_down],
  --            --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
  --          end end

  -- definition kshift_equiv' [constructor] (k : ℕ) : seq_colim f ≃ seq_colim (kshift_diag' f k) :=
  -- equiv.MK (kshift_up' f k)
  --          (kshift_down' f k)
  --          abstract begin
  --            intro a, exact sorry,
  --            -- induction a,
  --            -- { esimp, exact glue a},
  --            -- { apply eq_pathover,
  --            --   rewrite [▸*, ap_id, ap_compose shift_up shift_down, ↑shift_down,
  --            --            @elim_glue (λk, A (succ k)) _, ↑shift_up],
  --            --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
  --          end end
  --          abstract begin
  --            intro a, exact sorry
  --            -- induction a,
  --            -- { exact glue a},
  --            -- { apply eq_pathover,
  --            --   rewrite [▸*, ap_id, ap_compose shift_down shift_up, ↑shift_up,
  --            --            @elim_glue A _, ↑shift_down],
  --            --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
  --          end end

  variable {A}

  /- functorial action and equivalences -/
  section functor
  variable {f}
  variables {A' : ℕ → Type} {f' : seq_diagram A'}
  variables (g : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a))
  include p

  definition seq_colim_functor [unfold 7] : seq_colim f → seq_colim f' :=
  begin
    intro x, induction x with n a n a,
    { exact ι f' (g a)},
    { exact ap (ι f') (p a) ⬝ glue f' (g a)}
  end

  theorem seq_colim_functor_glue {n : ℕ} (a : A n)
    : ap (seq_colim_functor g p) (glue f a) = ap (ι f') (p a) ⬝ glue f' (g a) :=
  !elim_glue

  omit p

  definition is_equiv_seq_colim_functor [constructor] [H : Πn, is_equiv (@g n)]
     : is_equiv (seq_colim_functor @g p) :=
  adjointify _ (seq_colim_functor (λn, (@g _)⁻¹) (λn a, inv_commute' g f f' p a))
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (right_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor g p) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con, ▸*,
                   seq_colim_functor_glue _ _ ((@g _)⁻¹ a), -ap_compose, ↑[function.compose],
                   ap_compose (ι _) (@g _),ap_inv_commute',+ap_con, con.assoc,
                   +ap_inv, inv_con_cancel_left, con.assoc, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (left_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor _ _) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con,▸*, seq_colim_functor_glue _ _ (g a),
                   -ap_compose, ↑[function.compose], ap_compose (ι _) (@g _)⁻¹, inv_commute'_fn,
                   +ap_con, con.assoc, con.assoc, +ap_inv, con_inv_cancel_left, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end

  definition seq_colim_equiv [constructor] (g : Π{n}, A n ≃ A' n)
    (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a)) : seq_colim f ≃ seq_colim f' :=
  equiv.mk _ (is_equiv_seq_colim_functor @g p)

  definition seq_colim_rec_unc [unfold 4] {P : seq_colim f → Type}
    (v : Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
                   Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
    : Π(x : seq_colim f), P x :=
  by induction v with Pincl Pglue; exact seq_colim.rec f Pincl Pglue

  definition is_equiv_seq_colim_rec (P : seq_colim f → Type) :
    is_equiv (seq_colim_rec_unc :
      (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
        Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
          → (Π (aa : seq_colim f), P aa)) :=
  begin
    fapply adjointify,
    { intro s, exact ⟨λn a, s (ι f a), λn a, apd s (glue f a)⟩},
    { intro s, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover_dep, esimp, apply hdeg_squareover, apply rec_glue}},
    { intro v, induction v with Pincl Pglue, fapply ap (sigma.mk _),
      apply eq_of_homotopy2, intros n a, apply rec_glue},
  end

  /- universal property -/
  definition equiv_seq_colim_rec (P : seq_colim f → Type) :
    (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
       Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a) ≃ (Π (aa : seq_colim f), P aa) :=
  equiv.mk _ !is_equiv_seq_colim_rec

  end functor

  definition seq_colim_constant_seq (X : Type) : seq_colim (constant_seq X) ≃ X :=
  (equiv.mk _ (is_equiv_ι _ (λn, !is_equiv_id)))⁻¹ᵉ

  definition is_contr_seq_colim {A : ℕ → Type} (f : seq_diagram A)
    [Πk, is_contr (A k)] : is_contr (seq_colim f) :=
  begin
    apply @is_trunc_is_equiv_closed (A 0),
    apply is_equiv_ι, intro n, apply is_equiv_of_is_contr
  end

  /- colimits of dependent sequences, sigma's commute with colimits -/

  section over

  universe variable v
  variable {f}
  variables {P : Π⦃n⦄, A n → Type.{v}} (g : seq_diagram_over f P) {n : ℕ} {a : A n}

  definition rep_f_equiv_natural {k : ℕ} (p : P (rep f k (f a))) :
    transporto P (rep_f f (succ k) a) (g p) = g (transporto P (rep_f f k a) p) :=
  (fn_tro_eq_tro_fn2 (rep_f f k a) g p)⁻¹

  variable (a)
  definition over_f_equiv [constructor] :
    seq_colim (seq_diagram_of_over g (f a)) ≃ seq_colim (shift_diag (seq_diagram_of_over g a)) :=
  seq_colim_equiv (rep_f_equiv f P a) (λk p, rep_f_equiv_natural g p)

  definition seq_colim_over_equiv :
    seq_colim (seq_diagram_of_over g (f a)) ≃ seq_colim (seq_diagram_of_over g a) :=
  over_f_equiv g a ⬝e (shift_equiv (λk, P (rep f k a)) (seq_diagram_of_over g a))⁻¹ᵉ
  variable {a}

  include g
  definition seq_colim_over [unfold 5] (x : seq_colim f) : Type.{v} :=
  begin
    refine seq_colim.elim_type f _ _ x,
    { intro n a, exact seq_colim (seq_diagram_of_over g a)},
    { intro n a, exact seq_colim_over_equiv g a }
  end
  omit g

  definition ιo [constructor] (p : P a) : seq_colim_over g (ι f a) :=
  ι' _ 0 p

  -- Warning: the order of addition has changed in rep_rep
  -- definition rep_equiv_rep_rep (l : ℕ)
  --   : @seq_colim (λk, P (rep (k + l) a)) (kshift_diag' _ _) ≃
  --   @seq_colim (λk, P (rep k (rep l a))) (seq_diagram_of_over P (rep l a)) :=
  -- seq_colim_equiv (λk, rep_rep_equiv P a k l) abstract (λk p,
  --   begin
  --     esimp,
  --     rewrite [+cast_apd011],
  --     refine _ ⬝ (fn_tro_eq_tro_fn (rep_f k a)⁻¹ᵒ g p)⁻¹ᵖ,
  --     rewrite [↑rep_f,↓rep_f k a],
  --     refine !pathover_ap_invo_tro ⬝ _,
  --     rewrite [apo_invo,apo_tro]
  --   end) end

  variable {P}
  theorem seq_colim_over_glue (x : seq_colim_over g (ι f (f a)))
    : transport (seq_colim_over g) (glue f a) x = shift_down _ (over_f_equiv g a x) :=
  ap10 (elim_type_glue _ _ _ a) x

  theorem seq_colim_over_glue_inv (x : seq_colim_over g (ι f a))
    : transport (seq_colim_over g) (glue f a)⁻¹ x = to_inv (over_f_equiv g a) (shift_up _ x) :=
  ap10 (elim_type_glue_inv _ _ _ a) x

  definition glue_over (p : P (f a)) : pathover (seq_colim_over g) (ιo g p) (glue f a) (ι' _ 1 p) :=
  pathover_of_tr_eq !seq_colim_over_glue

-- we can define a function from the colimit of total spaces to the total space of the colimit.

definition sigma_colim_of_colim_sigma [unfold 5] (a : seq_colim (seq_diagram_sigma g)) :
  Σ(x : seq_colim f), seq_colim_over g x :=
begin
induction a with n v n v,
{ induction v with a p, exact ⟨ι f a, ιo g p⟩},
{ induction v with a p, fapply sigma_eq,
    apply glue,
    exact glue_over g (g p) ⬝op glue _ p}
end

definition colim_sigma_triangle [unfold 5] (a : seq_colim (seq_diagram_sigma g)) :
  (sigma_colim_of_colim_sigma g a).1 = seq_colim_functor (λn, sigma.pr1) (λn, homotopy.rfl) a :=
begin
induction a with n v n v,
{ induction v with a p, reflexivity },
{ induction v with a p, apply eq_pathover, apply hdeg_square,
  refine ap_compose sigma.pr1 _ _ ⬝ ap02 _ !elim_glue ⬝ _ ⬝ !elim_glue⁻¹,
  exact !sigma_eq_pr1 ⬝ !idp_con⁻¹ }
end

-- we now want to show that this function is an equivalence.

/-
  Kristina's proof of the induction principle of colim-sigma for sigma-colim.
  It's a double induction, so we have 4 cases: point-point, point-path, path-point and path-path.
  The main idea of the proof is that for the path-path case you need to fill a square, but we can
  define the point-path case as a filler for this square.
-/

open sigma

/-
  dictionary:
  Kristina | Lean
  VARIABLE NAMES (A, P, k, n, e, w are the same)
  x : A_n | a : A n
  a : A_n → A_{n+1} | f : A n → A (n+1)
  y : P(n, x) | x : P a (maybe other variables)
  f : P(n, x) → P(n+1, a_n x) | g : P a → P (f a)
  DEFINITION NAMES
  κ | glue
  U | rep_f_equiv : P (n+1+k, rep f k (f x)) ≃ P (n+k+1, rep f (k+1) x)
  δ | rep_f_equiv_natural
  F | over_f_equiv g a ⬝e (shift_equiv (λk, P (rep f k a)) (seq_diagram_of_over g a))⁻¹ᵉ
-/

/- the special case of "dpath" we use in the proof -/
definition Kristina_dpath (k : ℕ) (x : P (rep f k (f a))) :
  ⟨ι f (f a), ι (seq_diagram_of_over g (f a)) x⟩ =
  ⟨ι f a, ι (seq_diagram_of_over g a) (to_fun (rep_f_equiv f P a k) x)⟩
  :> sigma (seq_colim_over g) :=
begin
  apply dpair_eq_dpair (glue f a),
  apply pathover_of_tr_eq,
  refine seq_colim_over_glue g (ι (seq_diagram_of_over g (f a)) x)
end

definition Kristina_dpath_eq (k : ℕ) (x : P (rep f k (f a))) :
  Kristina_dpath g k x =
  dpair_eq_dpair (glue f a) (pathover_tr (glue f a) (ι (seq_diagram_of_over g (f a)) x)) ⬝
  ap (dpair (ι f a)) (seq_colim_over_glue g (ι (seq_diagram_of_over g (f a)) x)) :=
ap (sigma_eq _) !pathover_of_tr_eq_eq_concato ⬝ !sigma_eq_con ⬝ whisker_left _ !ap_dpair⁻¹

definition glue' (x : P a) :
  ⟨ι f (f a), ιo g (g x)⟩ = ⟨ι f a, ιo g x⟩ :> sigma (seq_colim_over g) :=
Kristina_dpath g 0 (g x) ⬝ ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x)

definition Kristina_gs_step {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Πn (a : A n) (x : P a), E ⟨ι f a, ιo g x⟩) {k : ℕ}
  (IH : Π{n} {a : A n} (x : P (rep f k a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩) :
  Σ(gs : Π⦃n : ℕ⦄ {a : A n} (x : P (rep f (k+1) a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩),
  Π⦃n : ℕ⦄ {a : A n} (x : P (rep f k (f a))),
    pathover E (IH x) (Kristina_dpath g k x) (gs (transporto P (rep_f f k a) x)) :=
begin
  fconstructor,
  { intro n a,
    refine equiv_rect (rep_f_equiv f P a k) _ _,
    intro z, refine transport E _ (IH z),
    exact Kristina_dpath g k z },
  { intro n a x, exact !pathover_tr ⬝op !equiv_rect_comp⁻¹ }
end

definition Kristina_gs /- g_* -/ {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Πn (a : A n) (x : P a), E ⟨ι f a, ιo g x⟩) {k : ℕ} :
  Π {n : ℕ} {a : A n} (x : P (rep f k a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩ :=
begin
  induction k with k IH: intro n a x,
  { exact e n a x },
  { apply (Kristina_gs_step g e @IH).1 }
end

definition Kristina_gs_path_left {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  {k : ℕ} {n : ℕ} {a : A n} (x : P (rep f k (f a))) :
  pathover E (Kristina_gs g e x) (Kristina_dpath g k x)
             (Kristina_gs g e (transporto P (rep_f f k a) x)) :=
by apply (Kristina_gs_step g e (@(Kristina_gs g e) k)).2

/- this is the bottom of the square we have to fill in the end -/
definition bottom_square {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a))) :=
move_top_of_right (natural_square
    (λ b, dpair_eq_dpair (glue f a) (pathover_tr (glue f a) b) ⬝
      ap (dpair (ι f a)) (seq_colim_over_glue g b))
    (glue (seq_diagram_of_over g (f a)) x) ⬝hp
  ap_compose (dpair (ι f a)) (to_fun (seq_colim_over_equiv g a))
    (glue (seq_diagram_of_over g (f a)) x) ⬝hp
  (ap02 (dpair (ι f a))
    (ap_compose (shift_down (seq_diagram_of_over g a)) (to_fun (over_f_equiv g a))
      (glue (seq_diagram_of_over g (f a)) x) ⬝
    ap02 (shift_down (seq_diagram_of_over g a)) (elim_glue _ _ _ x) ⬝
    ap_con (shift_down (seq_diagram_of_over g a))
      (ap (ι (shift_diag (seq_diagram_of_over g a))) (rep_f_equiv_natural g x))
      (glue (shift_diag (seq_diagram_of_over g a)) (to_fun (rep_f_equiv f P a k) x)) ⬝
    (ap_compose' (shift_down (seq_diagram_of_over g a)) (ι (shift_diag (seq_diagram_of_over g a)))
      (rep_f_equiv_natural g x))⁻¹ ◾
    elim_glue (shift_diag (seq_diagram_of_over g a)) _ _ (to_fun (rep_f_equiv f P a k) x))⁻¹)⁻¹ ⬝hp
  ap_con (dpair (ι f a))
    (ap (λx, shift_down (seq_diagram_of_over g a) (ι (shift_diag (seq_diagram_of_over g a)) x))
      (rep_f_equiv_natural g x))
    (glue (seq_diagram_of_over g a) (to_fun (rep_f_equiv f P a k) x)))

/- this is the composition + filler -/
definition Kristina_gs_path_right_step {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a)))
  (IH : Π(n : ℕ) (a : A n) (x : P (rep f k a)),
  pathover E (Kristina_gs g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (Kristina_gs g e x)) :=
squareover_fill_r
  (bottom_square g e w k x)
  (change_path (Kristina_dpath_eq g (succ k) (g x)) (Kristina_gs_path_left g e w (g x)) ⬝o
    pathover_ap E (dpair (ι f a))
      (pathover_ap (λ (b : seq_colim (seq_diagram_of_over g a)), E ⟨ι f a, b⟩)
        (ι (seq_diagram_of_over g a)) (apd (Kristina_gs g e) (rep_f_equiv_natural g x))))
  (change_path (Kristina_dpath_eq g k x) (Kristina_gs_path_left g e w x))
  (IH (n+1) (f a) x)

/- this is just the composition -/
definition Kristina_gs_path_right_step1 {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a)))
  (IH : Π(n : ℕ) (a : A n) (x : P (rep f k a)),
  pathover E (Kristina_gs g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (Kristina_gs g e x)) :=
(Kristina_gs_path_right_step g e w k x IH).1

definition Kristina_gs_path_right {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k a)) :
  pathover E (Kristina_gs g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (Kristina_gs g e x) :=
begin
  revert n a x, induction k with k IH: intro n a x,
  { exact pathover_cancel_left !pathover_tr⁻¹ᵒ (w x) },
  { revert x, refine equiv_rect (rep_f_equiv f P a k) _ _, intro x,
    exact Kristina_gs_path_right_step1 g e w k x IH }
end

definition Kristina_g [unfold 10] {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  {n : ℕ} {a : A n} (x : seq_colim_over g (ι f a)) : E ⟨ι f a, x⟩ :=
begin
  induction x with k x k x,
  { exact Kristina_gs g e x },
  { apply pathover_of_pathover_ap E (dpair (ι f a)),
    exact Kristina_gs_path_right g e w k x }
end

definition sigma_colim_rec {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (v : Σ(x : seq_colim f), seq_colim_over g x) : E v :=
begin
  induction v with x y,
  induction x with n a n a,
  { exact Kristina_g g e w y },
  { apply pi_pathover_left', intro x,
    refine change_path (whisker_left _ !ap_inv ⬝ !con_inv_cancel_right)
      (_ ⬝o pathover_ap E (dpair _) (apd (Kristina_g g e w) !seq_colim_over_glue⁻¹)),
    induction x with k x k x,
    { exact change_path !Kristina_dpath_eq (Kristina_gs_path_left g e w x) },
    { apply pathover_pathover,
      refine _ ⬝hop (ap (pathover_ap E _) (apd_compose2 (Kristina_g g e w) _ _) ⬝
        pathover_ap_pathover_of_pathover_ap E (dpair (ι f a)) (seq_colim_over_equiv g a) _)⁻¹,
      apply squareover_change_path_right',
      refine _ ⬝hop !pathover_ap_change_path⁻¹ ⬝ ap (pathover_ap E _)
        (apd02 _ (ap_compose (shift_down (seq_diagram_of_over g a)) _ _ ⬝ ap02 _ !elim_glue ⬝
        !ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_glue)⁻¹),
      apply squareover_change_path_right,
      refine _ ⬝hop (ap (pathover_ap E _) (!apd_con ⬝ (!apd_ap ◾o idp)) ⬝ !pathover_ap_cono)⁻¹,
      apply squareover_change_path_right',
      apply move_right_of_top_over,
      refine _ ⬝hop (ap (pathover_ap E _) !rec_glue ⬝ to_right_inv !pathover_compose _)⁻¹,
      refine ap (pathover_ap E _) !rec_glue ⬝ to_right_inv !pathover_compose _ ⬝pho _,
      refine _ ⬝hop !equiv_rect_comp⁻¹,
      exact (Kristina_gs_path_right_step g e w k x @(Kristina_gs_path_right g e w k)).2 }}
end

  /- We now define the map back, and show using this induction principle that the composites are the identity -/
  variable {P}

  definition colim_sigma_of_sigma_colim_constructor [unfold 7] (p : seq_colim_over g (ι f a))
    : seq_colim (seq_diagram_sigma g) :=
  begin
    induction p with k p k p,
    { exact ι _ ⟨rep f k a, p⟩},
    { apply glue}
  end

  definition colim_sigma_of_sigma_colim_path1 {k : ℕ} (p : P (rep f k (f a))) :
    ι (seq_diagram_sigma g) ⟨rep f k (f a), p⟩ =
    ι (seq_diagram_sigma g) ⟨rep f (succ k) a, transporto P (rep_f f k a) p⟩ :=
  begin
    apply apd0111 (λn a p, ι' (seq_diagram_sigma g) n ⟨a, p⟩) (succ_add n k) (rep_f f k a),
    apply pathover_tro
  end

  definition colim_sigma_of_sigma_colim_path2 {k : ℕ} (p : P (rep f k (f a))) :
  square (colim_sigma_of_sigma_colim_path1 g (g p)) (colim_sigma_of_sigma_colim_path1 g p)
    (ap (colim_sigma_of_sigma_colim_constructor g) (glue (seq_diagram_of_over g (f a)) p))
    (ap (λx, colim_sigma_of_sigma_colim_constructor g (shift_down (seq_diagram_of_over g a)
          (seq_colim_functor (λk, transporto P (rep_f f k a)) (λk p, rep_f_equiv_natural g p) x)))
      (glue (seq_diagram_of_over g (f a)) p)) :=
  begin
    refine !elim_glue ⬝ph _,
    refine _ ⬝hp (ap_compose' (colim_sigma_of_sigma_colim_constructor g ∘ shift_down _) _ _)⁻¹,
    refine _ ⬝hp ap02 _ !elim_glue⁻¹,
    refine _ ⬝hp !ap_con⁻¹,
    refine _ ⬝hp (!ap_compose' ◾ (ap_compose _ _ _)⁻¹),
    refine _ ⬝hp whisker_left _ (ap02 _ !elim_glue⁻¹),
    refine _ ⬝hp whisker_left _ !elim_glue⁻¹,
    refine _ ⬝pv whisker_rt _ (natural_square0111 P (pathover_tro (rep_f f k a) p) g
                                                    (λn a p, glue (seq_diagram_sigma g) ⟨a, p⟩)),
    refine _ ⬝ whisker_left _ (ap02 _ !inv_inv⁻¹ ⬝ !ap_inv),
    symmetry, apply apd0111_precompose
  end

  definition colim_sigma_of_sigma_colim [unfold 5] (v : Σ(x : seq_colim f), seq_colim_over g x)
    : seq_colim (seq_diagram_sigma g) :=
  begin
    induction v with x p,
    induction x with n a n a,
    { exact colim_sigma_of_sigma_colim_constructor g p },
    apply arrow_pathover_constant_right, intro x, esimp at x,
    refine _ ⬝ ap (colim_sigma_of_sigma_colim_constructor g) !seq_colim_over_glue⁻¹,
    induction x with k p k p,
    { exact colim_sigma_of_sigma_colim_path1 g p },
    apply eq_pathover, apply colim_sigma_of_sigma_colim_path2
  end

  theorem colim_sigma_of_sigma_colim_of_colim_sigma (a : seq_colim (seq_diagram_sigma g)) :
    colim_sigma_of_sigma_colim g (sigma_colim_of_colim_sigma g a) = a :=
  begin
  induction a with n v n v,
  { induction v with a p, reflexivity },
  { induction v with a p, esimp, apply eq_pathover_id_right, apply hdeg_square,
    refine ap_compose (colim_sigma_of_sigma_colim g) _ _ ⬝ _,
    refine ap02 _ !elim_glue ⬝ _, esimp,
    refine !ap_dpair_eq_dpair ⬝ _,
    refine !apd011_eq_apo11_apd ⬝ _,
    refine ap (λx, apo11_constant_right x _) !rec_glue ⬝ _,
    refine !apo11_arrow_pathover_constant_right ⬝ _,
    rewrite [▸*, tr_eq_of_pathover_concato_eq, ap_con, ↑glue_over,
             to_right_inv !pathover_equiv_tr_eq, ap_inv, con.assoc, inv_con_cancel_left],
    refine whisker_left _ !elim_glue ⬝ _,
    apply idp_con }
  end

  theorem sigma_colim_of_colim_sigma_of_sigma_colim (v : Σ(x : seq_colim f), seq_colim_over g x)
    : sigma_colim_of_colim_sigma g (colim_sigma_of_sigma_colim g v) = v :=
  begin
    revert v, refine sigma_colim_rec _ _ _,
    { intro n a x, reflexivity },
    { intro n a x, apply eq_pathover_id_right, apply hdeg_square,
      refine ap_compose (sigma_colim_of_colim_sigma g) _ _ ⬝ _,
      refine ap02 _ (!ap_con ⬝ (!ap_dpair_eq_dpair ⬝ !apd011_eq_apo11_apd ⬝
        ap (λx, apo11_constant_right x _) !rec_glue ⬝ !apo11_arrow_pathover_constant_right ⬝
        begin rewrite [▸*, ap_inv, to_right_inv !pathover_equiv_tr_eq, inv_con_cancel_right],
          reflexivity end) ◾ (!ap_compose'⁻¹ ⬝ !elim_glue)) ⬝ _,
      refine !ap_con ⬝ !idp_con ⬝ !elim_glue ⬝ _,
      refine _ ⬝ !sigma_eq_con ⬝ whisker_left _ !ap_dpair⁻¹,
      exact ap (sigma_eq _) !concato_eq_eq }
  end

  variable (P)
  definition sigma_seq_colim_over_equiv [constructor]
    : (Σ(x : seq_colim f), seq_colim_over g x) ≃ seq_colim (seq_diagram_sigma g) :=
  equiv.MK (colim_sigma_of_sigma_colim g)
           (sigma_colim_of_colim_sigma g)
           (colim_sigma_of_sigma_colim_of_colim_sigma g)
           (sigma_colim_of_colim_sigma_of_sigma_colim g)

  end over

end seq_colim


  -- We need a characterization of equality in seq_colim for the following results:


  -- definition is_prop_seq_colim {A : ℕ → Type} (f : seq_diagram A)
  --   [Πk, is_prop (A k)] : is_prop (seq_colim f) :=
  -- begin
  --   apply is_prop.mk,
  --   intro x,
  --   induction x using seq_colim.rec_prop with n a n a,
  -- end

  -- definition is_trunc_seq_colim (n : ℕ₋₂) {A : ℕ → Type} (f : seq_diagram A)
  --   [Πk, is_trunc n (A k)] : is_trunc n (seq_colim f) :=
  -- begin
  --   induction n with n IH,
  --   { fapply is_contr.mk,
  --     { exact ι' f 0 !center},
  --     { },
  --   { }
  -- end
