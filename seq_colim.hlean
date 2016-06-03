/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/
import hit.colimit .sequence cubical.squareover types.arrow .move_to_lib types.equiv

open eq nat sigma sigma.ops quotient equiv pi is_trunc is_equiv fiber function

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

  definition colim_back [unfold 4] [H : is_equiseq f] : seq_colim f → A 0 :=
  begin
    intro x,
    induction x with k a k a,
    { exact rep0_back f k a},
    rexact ap (rep0_back f k) (left_inv (@f k) a),
  end

  section
  local attribute is_equiv_rep0 [instance] [priority 500]
  definition equiseq_colim_equiv (H : is_equiseq f) : is_equiv (@ι A f 0) :=
  begin
    fapply adjointify,
    { exact colim_back f},
    { intro x, induction x with k a k a,
      { esimp,
        refine (rep0_glue f k (rep0_back f k a))⁻¹ ⬝ _,
        exact ap (ι f) (right_inv (rep0 f k) a)},
      apply eq_pathover_id_right,
      refine (ap_compose (ι f) (colim_back f) _) ⬝ph _,
      refine ap02 _ !elim_glue ⬝ph _, exact sorry},
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
    { exact ι _ (f a)},
    { exact glue _ (f a)}
  end

  definition shift_down [unfold 3] (x : seq_colim (shift_diag f)) : seq_colim f :=
  begin
    induction x,
    { exact ι f a},
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
             { esimp, exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_up f) (shift_down f), ↑shift_down,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end
           abstract begin
             intro x, induction x,
             { exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_down f) (shift_up f), ↑shift_up,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
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

  -- TODO: move:
  theorem inv_commute'_fn {A : Type} {B C : A → Type} (f : Π{a}, B a → C a)
    [H : Πa, is_equiv (@f a)]
    {g : A → A} (h : Π{a}, B a → B (g a)) (h' : Π{a}, C a → C (g a))
    (p : Π⦃a : A⦄ (b : B a), f (h b) = h' (f b)) {a : A} (b : B a) :
    inv_commute' @f @h @h' p (f b)
      = (ap f⁻¹ (p b))⁻¹ ⬝ left_inv f (h b) ⬝ (ap h (left_inv f b))⁻¹ :=
  begin
    rewrite [↑[inv_commute',eq_of_fn_eq_fn'],+ap_con,-adj_inv f,+con.assoc,inv_con_cancel_left,
       adj f,+ap_inv,-+ap_compose,
       eq_bot_of_square (natural_square (λb, (left_inv f (h b))⁻¹ ⬝ ap f⁻¹ (p b)) (left_inv f b))⁻¹ʰ,
       con_inv,inv_inv,+con.assoc],
    do 3 apply whisker_left,
    rewrite [con_inv_cancel_left,con.left_inv]
  end

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
  (equiv.mk _ (equiseq_colim_equiv _ (λn, !is_equiv_id)))⁻¹ᵉ

  definition is_contr_seq_colim {A : ℕ → Type} (f : seq_diagram A)
    [Πk, is_contr (A k)] : is_contr (seq_colim f) :=
  begin
    apply @is_trunc_is_equiv_closed (A 0),
    apply equiseq_colim_equiv, intro n, apply is_equiv_of_is_contr
  end

  /- colimits of dependent sequences, sigma's commute with colimits -/

  section over

  universe variable v
  variable {f}
  variables {P : Π⦃n⦄, A n → Type.{v}} (g : seq_diagram_over f P) {n : ℕ} {a : A n}

  definition rep_f_equiv_natural {k : ℕ} (p : P (rep f k (f a))) :
    transporto P (rep_f f (succ k) a) (g p) = g (transporto P (rep_f f k a) p) :=
  (my.fn_tro_eq_tro_fn2 (rep_f f k a) g p)⁻¹

  variable (a)
  definition over_f_equiv [constructor] :
    seq_colim (seq_diagram_of_over g (f a)) ≃ seq_colim (shift_diag (seq_diagram_of_over g a)) :=
  seq_colim_equiv (rep_f_equiv f P a) (λk p, rep_f_equiv_natural g p)
  variable {a}

  include g
  definition seq_colim_over [unfold 5] (x : seq_colim f) : Type.{v} :=
  begin
    refine seq_colim.elim_type f _ _ x,
    { intro n a, exact seq_colim (seq_diagram_of_over g a)},
    { intro n a, refine !over_f_equiv ⬝e !shift_equiv⁻¹ᵉ}
  end
  omit g

  definition ιo [constructor] (p : P a) : seq_colim_over g (ι f a) :=
  ι' _ 0 p

  -- definition rep_equiv_rep_rep (l : ℕ)
  --   : @seq_colim (λk, P (rep (k + l) a)) (kshift_diag' _ _) ≃
  --   @seq_colim (λk, P (rep k (rep l a))) (seq_diagram_of_over P (rep l a)) :=
  -- seq_colim_equiv (λk, rep_rep_equiv P a k l) abstract (λk p,
  --   begin
  --     esimp,
  --     rewrite [+my.cast_apo011],
  --     refine _ ⬝ (my.fn_tro_eq_tro_fn (rep_f k a)⁻¹ᵒ g p)⁻¹ᵖ,
  --     rewrite [↑rep_f,↓rep_f k a],
  --     refine !my.pathover_ap_invo_tro ⬝ _,
  --     rewrite [my.apo_invo,my.apo_tro]
  --   end) end


  variable {P}
  theorem seq_colim_over_glue (x : seq_colim_over g (ι f (f a)))
    : transport (seq_colim_over g) (glue f a) x = shift_down _ (over_f_equiv g a x) :=
  ap10 (elim_type_glue _ _ _ a) x
  -- REPORT: in the preceding proof, the following gives error:
  --   by exact ap10 (elim_type_glue _ _ _ a) x
  -- changing ap10 to ap10.{v v} resolves the error


  -- TODO: move
  theorem elim_type_glue_inv.{u} (Pincl : Π⦃n : ℕ⦄ (a : A n), Type.{u})
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
    : transport (seq_colim.elim_type f Pincl Pglue) (glue f a)⁻¹ = to_inv (Pglue a) :=
  by rewrite [tr_eq_cast_ap_fn, ↑seq_colim.elim_type, ap_inv, elim_glue]; apply cast_ua_inv_fn

  theorem seq_colim_over_glue_inv (x : seq_colim_over g (ι f a))
    : transport (seq_colim_over g) (glue f a)⁻¹ x = to_inv (over_f_equiv g a) (shift_up _ x) :=
  ap10 (elim_type_glue_inv _ _ a) x

  definition glue_over (p : P a) :
    pathover (seq_colim_over g) (ιo g (g p)) (glue f a) (ι' _ 1 (g p)) :=
  pathover_of_tr_eq !seq_colim_over_glue


  definition glue_over_gen (k : ℕ) (p : P (rep f k a)) :
    pathover (seq_colim_over g) (ι' (seq_diagram_of_over g (f a)) k ((rep_f f k a)⁻¹ᵒ ▸o g p))
             (glue f a)         (ι' (seq_diagram_of_over g a) (succ k) (g p)) :=
  sorry

  definition glue_over_rep (k : ℕ) (p : P (rep f k a)) :
    pathover (seq_colim_over g) (ιo g p) (rep_glue f k a) (ι' _ k p) :=
  begin
    revert a p, induction k with k IH, all_goals intro a p,
    { constructor},
    { change pathover (seq_colim_over g) (ιo g p)
                      (glue f (rep f k a) ⬝ rep_glue f k a) (ι' _ (succ k) p),
      exact sorry
      --refine !glue_over ⬝o _,
-- rewrite [↑seq_diagram_of_over,↑rep_glue],
--       refine !pathover_tr ⬝o _,
      -- refine eq_concato !glue⁻¹ _, esimp,
      -- refine !glue_over⁻¹ᵒ ⬝o _,
      -- exact sorry
    }
  end

  -- we can define a function from the colimit of total spaces to the total space of the colimit.

  definition sigma_colim_of_colim_sigma [unfold 5] (a : seq_colim (seq_diagram_sigma g)) :
    Σ(x : seq_colim f), seq_colim_over g x :=
  begin
  induction a with n v n v,
  { induction v with a p, exact ⟨ι f a, ιo g p⟩},
  { induction v with a p, esimp [seq_diagram_sigma], fapply sigma_eq,
      apply glue,
      esimp, exact glue_over g p ⬝op glue _ p}
  end

  -- we now want to show that this function is an equivalence.

  /- ATTEMPT 1: show that this function has contractible fibers -/
  theorem is_equiv_sigma_colim_of_colim_sigma : is_equiv (sigma_colim_of_colim_sigma g) :=
  begin
    apply @is_equiv_of_is_contr_fun,
    intro v,
    induction v with aa pp,
    induction aa using seq_colim.rec_prop,
    induction pp using seq_colim.rec_prop with k p,
    fapply is_contr.mk,
    { fapply fiber.mk,
      { exact ι _ ⟨rep f k a, p⟩},
      { esimp [sigma_colim_of_colim_sigma], fapply sigma_eq,
        { esimp, apply rep_glue},
        { esimp, rexact glue_over_rep g k p}}},
    { intro v, induction v with v q,
      induction v with l v l v,
      { induction v with a' p', esimp [sigma_colim_of_colim_sigma] at q,
        fapply fiber_eq,
        { esimp, exact sorry},
        { esimp, exact sorry}},
      { induction v with a' p', esimp, exact sorry}}
  end

  /- ATTEMPT 2: give the reverse function and show they are mutually inverses
    This attempt looks most promising. -/
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
    apply apo0111 (λn a p, ι' (seq_diagram_sigma g) n ⟨a, p⟩) (succ_add n k) (rep_f f k a),
    apply my.pathover_tro
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
    refine _ ⬝pv whisker_rt _ (my.natural_square0111 P (my.pathover_tro P (rep_f f k a) p) g
                                                     (λn a p, glue (seq_diagram_sigma g) ⟨a, p⟩)),
    refine _ ⬝ whisker_left _ (ap02 _ !inv_inv⁻¹ ⬝ !ap_inv),
    symmetry, apply my.apo0111_precompose
  end

  -- TODO: move
  definition arrow_pathover_constant_right_rev {A : Type} {B : A → Type} {C : Type} {a a' : A}
    {f : B a → C} {g : B a' → C} {p : a = a'} (r : Π(b : B a'), f (p⁻¹ ▸ b) = g b) : f =[p] g :=
  arrow_pathover_right (λb, pathover_of_eq (r b))

  definition colim_sigma_of_sigma_colim [unfold 5] (v : Σ(x : seq_colim f), seq_colim_over g x)
    : seq_colim (seq_diagram_sigma g) :=
  begin
    induction v with x p,
    induction x with n a n a,
    { exact colim_sigma_of_sigma_colim_constructor g p},
    esimp, apply arrow_pathover_constant_right, intro x, esimp at x,
    refine _ ⬝ ap (colim_sigma_of_sigma_colim_constructor g) !seq_colim_over_glue⁻¹,
    induction x with k p k p,
    { esimp, exact colim_sigma_of_sigma_colim_path1 g p},
    apply eq_pathover, apply colim_sigma_of_sigma_colim_path2
  end

  -- TODO: move (and rename)
  definition apo11' [unfold 12] {A X : Type} {B : A → Type} {a a' : A} {p : a = a'}
    {f : B a → X} {g : B a' → X} (q : f =[p] g) {b : B a} {b' : B a'} (r : b =[p] b') :
    f b = g b' :=
  begin
    induction r, exact ap10 (eq_of_pathover_idp q) b
  end

  -- TODO: make argument p in pathover_of_eq explicit
  -- TODO: move
  definition eq_of_pathover_idp_pathover_of_eq {A X : Type} (x : X) {a a' : A} (p : a = a') :
    eq_of_pathover_idp (@pathover_of_eq _ _ _ _ (idpath x)  _ _ p) = p :=
  by induction p; reflexivity

  -- TODO: move
  definition apo11'_arrow_pathover_constant_right {A X : Type} {B : A → Type} {a a' : A} {p : a = a'}
    {f : B a → X} {g : B a' → X} (q : Πb, f b = g (p ▸ b)) {b : B a} {b' : B a'} (r : b =[p] b') :
    apo11' (arrow_pathover_constant_right q) r = q b ⬝ ap g (tr_eq_of_pathover r) :=
  begin
    induction r, esimp at *,
    unfold [arrow_pathover_constant_right, arrow_pathover_left, ap10],
    rewrite [to_right_inv !pathover_idp],
    refine apd10 (to_right_inv !eq_equiv_homotopy _) b ⬝ _,
    apply eq_of_pathover_idp_pathover_of_eq
  end

  -- TODO: move
  definition ap_sigma_eq {A X : Type} {B : A → Type} (f : (Σa, B a) → X)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') :
    ap f (sigma_eq p q) = apo11' (apd (λa b, f ⟨a, b⟩) p) q :=
  by induction q; reflexivity

  -- TODO: move
  definition tr_eq_of_pathover_concato_eq {A : Type} {B : A → Type} {a a' : A} {p : a = a'}
    {b : B a} {b' b'' : B a'} (q : b =[p] b') (r : b' = b'') :
    tr_eq_of_pathover (q ⬝op r) = tr_eq_of_pathover q ⬝ r :=
  by induction r; reflexivity

  theorem colim_sigma_of_sigma_colim_of_colim_sigma (a : seq_colim (seq_diagram_sigma g)) :
    colim_sigma_of_sigma_colim g (sigma_colim_of_colim_sigma g a) = a :=
  begin
  induction a with n v n v,
  { induction v with a p, reflexivity},
  { induction v with a p, esimp, apply eq_pathover_id_right, apply hdeg_square,
    refine ap_compose (colim_sigma_of_sigma_colim g) _ _ ⬝ _,
    refine ap02 _ !elim_glue ⬝ _, esimp,
    refine !ap_sigma_eq ⬝ _,
    refine ap (λx, apo11' x _) !rec_glue ⬝ _,
    refine !apo11'_arrow_pathover_constant_right ⬝ _,
    rewrite [▸*, tr_eq_of_pathover_concato_eq, ap_con, ↑glue_over,
             to_right_inv !pathover_equiv_tr_eq, ap_inv, con.assoc, inv_con_cancel_left],
    refine whisker_left _ !elim_glue ⬝ _,
    apply idp_con}
  end

  definition sigma_colim_of_colim_sigma_of_sigma_colim_constructor [unfold 7]
    (p : seq_colim_over g (ι f a)) :
    sigma_colim_of_colim_sigma g (colim_sigma_of_sigma_colim g ⟨ι f a, p⟩) = ⟨ι f a, p⟩ :=
  begin
    induction p with k p k p,
    { apply sigma_eq (rep_glue f k a), esimp, apply (glue_over_rep g k p)},
    { apply eq_pathover, esimp, exact sorry }
  end

  theorem sigma_colim_of_colim_sigma_of_sigma_colim (v : Σ(x : seq_colim f), seq_colim_over g x)
    : sigma_colim_of_colim_sigma g (colim_sigma_of_sigma_colim g v) = v :=
  begin
    induction v with x p,
    induction x with n a n a,
    { apply sigma_colim_of_colim_sigma_of_sigma_colim_constructor},
    apply pi_pathover_left, intro x, esimp at x,
    exact sorry
    -- refine _ ⬝ ap (colim_sigma_of_sigma_colim_constructor g) !seq_colim_over_glue⁻¹,
    -- induction x with k p k p,
    -- { esimp, exact colim_sigma_of_sigma_colim_path1 g p},
    -- apply eq_pathover, apply colim_sigma_of_sigma_colim_path2
  end

  variable (P)
  definition seq_colim_over_equiv [constructor]
    : (Σ(x : seq_colim f), seq_colim_over g x) ≃ seq_colim (seq_diagram_sigma g) :=
  equiv.MK (colim_sigma_of_sigma_colim g)
           (sigma_colim_of_colim_sigma g)
           (colim_sigma_of_sigma_colim_of_colim_sigma g)
           (sigma_colim_of_colim_sigma_of_sigma_colim g)


  /- ATTEMPT 3: try to prove the equivalence by using flattening -/

  /-
  definition goal_def1 : seq_diagram_over (λ (n : ℕ) (x : A n), seq_colim (λ (k : ℕ), P (rep k x))) :=
  begin
    intro n a x,
    apply shift_diag P,
  end

  definition goal : @(seq_colim (λn, Σ(x : A n), seq_colim (λk, P (rep k x)))) begin end
                    ≃ seq_colim (λn, Σ(x : A n), P x) :=
  _
  -/

  end over

  /- ATTEMPT 4: try to prove the equivalence by proving the induction principle and computation rules
     of the colimit-of-sigma's for the sigma-of-colimits. This is the same technique used
     in the proof for the flattening lemma -/


  -- namespace sigma_colim

  -- variables (P : Π⦃n⦄, A n → Type) [g : seq_diagram_over P]
  -- include g

  -- definition Sincl (v : Σ(x : A n), P x) : Σ(x : seq_colim A), seq_colim_over P x :=
  -- ⟨ι v.1, @ι _ _ 0 v.2⟩

  -- definition Sglue (v : Σ(x : A n), P x) : Sincl P (seq_diagram_sigma P v) = Sincl P v :=
  -- sigma_eq !glue (!glue_over ⬝op glue v.2)

  -- protected definition rec {Q : (Σ(x : seq_colim A), seq_colim_over P x) → Type}
  --   (Qincl : Π⦃n : ℕ⦄ (v : Σ(x : A n), P x), Q (Sincl P v))
  --   (Qglue : Π⦃n : ℕ⦄ (v : Σ(x : A n), P x), Qincl (seq_diagram_sigma P v) =[Sglue P v] Qincl v)
  --   (v : Σ(x : seq_colim A), seq_colim_over P x) : Q v :=
  -- sorry

  -- end sigma_colim


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
