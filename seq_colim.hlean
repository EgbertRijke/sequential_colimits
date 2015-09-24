/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/
import hit.quotient .sequence cubical.squareover types.arrow .move_to_lib types.equiv

open eq nat sigma sigma.ops quotient equiv equiv.ops pi is_trunc is_equiv fiber

namespace seq_colim

  section
  parameters (A : ℕ → Type) [f : seq_diagram A]
  variables {n : ℕ} (a : A n)
  include f

  local abbreviation B := Σ(n : ℕ), A n
  inductive seq_rel : B → B → Type :=
  | Rmk : Π{n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local abbreviation R := seq_rel

  definition seq_colim : Type :=
  quotient seq_rel

  parameters {A f}
  variable (n)
  -- do we want to make n explicit for ι? 'ι a' is ambiguous for a : A n. It can be 'ι n a' or 'ι 0 a' in a shifted sequence
  definition inclusion [constructor] : seq_colim :=
  class_of R ⟨n, a⟩

  abbreviation ι' [constructor] := @inclusion
  variable {n}
  abbreviation ι [constructor] [parsing-only] := @inclusion n

  definition glue : ι (f a) = ι a :=
  eq_of_rel seq_rel (Rmk a)

  protected definition rec {P : seq_colim → Type}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (ι a))
    (Pglue : Π(n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) (aa : seq_colim) : P aa :=
  begin
    fapply (quotient.rec_on aa),
    { intro a, cases a, apply Pincl},
    { intro a a' H, cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : seq_colim → Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (ι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  theorem rec_glue {P : seq_colim → Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (ι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a) {n : ℕ} (a : A n)
      : apdo (rec Pincl Pglue) (glue a) = Pglue a :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim → P :=
  rec Pincl (λn a, pathover_of_eq (Pglue a))

  protected definition elim_on [reducible] {P : Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  theorem elim_glue {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = Pglue a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue a)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : seq_colim → Type :=
  elim Pincl (λn a, ua (Pglue a))

  protected definition elim_type_on [reducible] (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : Type :=
  elim_type Pincl Pglue aa

  theorem elim_type_glue (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
      : transport (elim_type Pincl Pglue) (glue a) = Pglue a :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end
end seq_colim

attribute seq_colim.inclusion seq_colim.ι [constructor]
attribute seq_colim.rec seq_colim.elim [unfold 6] [recursor 6]
attribute seq_colim.elim_type [unfold 5]
attribute seq_colim.rec_on seq_colim.elim_on [unfold 4]
attribute seq_colim.elim_type_on [unfold 3]

namespace seq_colim

  variables {A : ℕ → Type} [f : seq_diagram A]
  include f

  definition rep0_glue (k : ℕ) (a : A 0) : @ι _ _ _ (rep0 k a) = ι a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue (rep0 k a) ⬝ IH}
  end

  definition equiseq_colim_back [H : is_equiseq f] : seq_colim A → A 0 :=
  begin
    intro x,
    induction x with n a,
    apply (rep0 n)⁻¹,
    exact a,
    refine _ ⬝ (ap ((rep0 n)⁻¹ᶠ) (left_inv (@f _) a)),
    unfold rep0,
  end

  definition equiseq_colim_equiv (H : is_equiseq f) : is_equiv (@inclusion A f 0) :=
  begin
    fapply adjointify,
    exact equiseq_colim_back,
    intro x; induction x with n a,
    unfold equiseq_colim_back,
    esimp,
    refine (rep0_glue n ((rep0 n)⁻¹ a))⁻¹ ⬝ _,
    exact ap (ι' n) (right_inv (rep0 n) a),
    exact sorry,
    intro a,
    exact rfl,
  end

  variables {n : ℕ} (a : A n)

  definition rep_glue (k : ℕ) : @ι _ _ _ (rep k a) = ι a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue (rep k a) ⬝ IH}
  end

  definition shift_up [unfold 3] (a : seq_colim A) : seq_colim (λk, A (succ k)) :=
  begin
    induction a,
    { exact ι (f a)},
    { exact glue (f a)}
  end

  definition shift_down [unfold 3] (a : seq_colim (λn, A (succ n))) : seq_colim A :=
  begin
    induction a,
    { exact ι a},
    { exact glue a}
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

  definition kshift_up' (k : ℕ) (a : seq_colim A) : @seq_colim (λn, A (n + k)) (kshift_diag' A k) :=
  begin
    induction a,
    { apply ι' n, exact rep k a},
    { exact sorry}
  end

  definition kshift_down' (k : ℕ) (a : @seq_colim (λn, A (n + k)) (kshift_diag' A k)) : seq_colim A :=
  begin
    induction a,
    { exact ι a},
    { esimp, exact sorry}
  end

  variable (A)
  definition shift_equiv [constructor] : seq_colim A ≃ seq_colim (λn, A (succ n)) :=
  equiv.MK shift_up
           shift_down
           abstract begin
             intro a, induction a,
             { esimp, exact glue a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose shift_up shift_down, ↑shift_down,
                        @elim_glue (λk, A (succ k)) _, ↑shift_up],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end
           abstract begin
             intro a, induction a,
             { exact glue a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose shift_down shift_up, ↑shift_up,
                        @elim_glue A _, ↑shift_down],
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

  definition kshift_equiv' [constructor] (k : ℕ)
    : seq_colim A ≃ @seq_colim (λn, A (n + k)) (kshift_diag' A k) :=
  equiv.MK (kshift_up' k)
           (kshift_down' k)
           abstract begin
             intro a, exact sorry,
             -- induction a,
             -- { esimp, exact glue a},
             -- { apply eq_pathover,
             --   rewrite [▸*, ap_id, ap_compose shift_up shift_down, ↑shift_down,
             --            @elim_glue (λk, A (succ k)) _, ↑shift_up],
             --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end
           abstract begin
             intro a, exact sorry
             -- induction a,
             -- { exact glue a},
             -- { apply eq_pathover,
             --   rewrite [▸*, ap_id, ap_compose shift_down shift_up, ↑shift_up,
             --            @elim_glue A _, ↑shift_down],
             --   apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end

  variable {A}

  /- functorial action and equivalences -/
  section functor
  variables {A' : ℕ → Type} [f' : seq_diagram A']
  variables (g : Π{n}, A n → A' n) (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a))
  include p

  definition seq_colim_functor [unfold 7] : seq_colim A → seq_colim A' :=
  seq_colim.elim (λn a, ι (g a)) (λn a, ap ι (p a) ⬝ glue (g a))

  theorem seq_colim_functor_glue {n : ℕ} (a : A n)
    : ap (seq_colim_functor @g p) (glue a) = ap ι (p a) ⬝ glue (g a) :=
  !elim_glue

  omit p f

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

  include f p
  --set_option pp.notation false
  definition is_equiv_seq_colim_functor [constructor] [H : Πn, is_equiv (g : A n → A' n)]
     : is_equiv (seq_colim_functor @g p) :=
  adjointify _ (seq_colim_functor (λn, g⁻¹) (λn a, inv_commute' @g @f @f' p a))
             abstract begin
               intro x, induction x,
               { esimp, exact ap ι (right_inv g a)},
               { apply eq_pathover,
                 rewrite [ap_id,ap_compose (seq_colim_functor @g p) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a,ap_con,▸*,seq_colim_functor_glue _ _ (g⁻¹ a),
                   -ap_compose,↑[function.compose],ap_compose ι g,ap_inv_commute',+ap_con,con.assoc,
                   +ap_inv,inv_con_cancel_left,con.assoc,-ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apdo}
             end end
             abstract begin
               intro x, induction x,
               { esimp, exact ap ι (left_inv g a)},
               { apply eq_pathover,
                 rewrite [ap_id,ap_compose (seq_colim_functor _ _) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a,ap_con,▸*,seq_colim_functor_glue _ _ (g a),
                   -ap_compose,↑[function.compose],ap_compose ι g⁻¹,inv_commute'_fn,+ap_con,
                   con.assoc,con.assoc,+ap_inv,con_inv_cancel_left,-ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apdo}
             end end

  omit p
  variables {f f'}
  definition seq_colim_equiv [constructor] (g : Π{n}, A n ≃ A' n)
    (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a)) : seq_colim A ≃ seq_colim A' :=
  equiv.mk _ (is_equiv_seq_colim_functor @g p)

  definition seq_colim_rec_unc [unfold 4] {P : seq_colim A → Type}
    (v : Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι a)),
                   Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[ glue a ] Pincl a)
    : Π(x : seq_colim A), P x :=
  by induction v with Pincl Pglue ;exact seq_colim.rec Pincl Pglue

  omit f
  definition eq_pathover_dep {A : Type} {B : A → Type} {a a' : A}
    {f g : Πa, B a} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : squareover B !hrfl (pathover_idp_of_eq q) (pathover_idp_of_eq r) (apdo f p) (apdo g p))
      : q =[p] r :=
  begin
    induction p, apply pathover_idp_of_eq,
    let H  := pathover_of_vdeg_squareover s,
    let H' := eq_of_pathover_idp H,
    exact eq_of_fn_eq_fn !pathover_idp⁻¹ᵉ H',
  end
  include f

  definition is_equiv_seq_colim_rec (P : seq_colim A → Type) :
    is_equiv (seq_colim_rec_unc :
      (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι a)),
        Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[ glue a ] Pincl a)
          → (Π (aa : seq_colim A), P aa)) :=
  begin
    fapply adjointify,
    { intro f, exact ⟨λn a, f (ι a), λn a, apdo f (glue a)⟩},
    { intro f, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover_dep, esimp, apply hdeg_squareover, apply rec_glue}},
    { intro v, induction v with Pincl Pglue, fapply ap (sigma.mk _),
      apply eq_of_homotopy2, intros n a, apply rec_glue},
  end

  definition equiv_seq_colim_rec (P : seq_colim A → Type) :
    (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι a)),
       Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[ glue a ] Pincl a) ≃ (Π (aa : seq_colim A), P aa) :=
  equiv.mk _ !is_equiv_seq_colim_rec

  end functor

  /- colimits of dependent sequences, sigma's commute with colimits -/

  section over

  universe variable v
  variables (P : Π⦃n⦄, A n → Type.{v}) [g : seq_diagram_over P]
  include g

  definition f_rep_equiv_rep_f
    : @seq_colim (λk, P (rep (succ k) a)) _ ≃
    @seq_colim (λk, P (rep k (f a))) (seq_diagram_of_over P (f a)) :=
  seq_colim_equiv (rep_f_equiv P a) abstract (λk p,
    begin
      esimp,
      rewrite [+my.cast_apo011],
      refine _ ⬝ (my.fn_tro_eq_tro_fn (rep_f k a)⁻¹ᵒ g p)⁻¹,
      rewrite [↑rep_f,↓rep_f k a],
      refine !my.pathover_ap_invo_tro ⬝ _,
      rewrite [my.apo_invo,my.apo_tro]
    end) end

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


  definition seq_colim_over [unfold 5] (x : seq_colim A) : Type.{v} :=
  begin
    fapply seq_colim.elim_type_on x,
    { intro n a, exact seq_colim (λk, P (rep k a))},
    { intro n a, symmetry,
      refine !shift_equiv ⬝e !f_rep_equiv_rep_f}
  end

  variable {P}
  -- theorem seq_colim_over_glue (x : seq_colim_over P (ι (f a)))
  --   : transport (seq_colim_over P) (glue a) x = shift_down ((to_fun (f_rep_equiv_rep_f a P))⁻¹ x) :=
  -- ap10 (elim_type_glue _ _ a) x
  -- REPORT: the following gives error: by exact ap10 (elim_type_glue _ _ a) x
  -- changing ap10 to ap10.{v v} resolves the error

  definition seq_colim_over_glue (x : seq_colim_over P (ι (f a)))
    : pathover (seq_colim_over P) x (glue a) (shift_down (to_inv (f_rep_equiv_rep_f a P) x)) :=
-- pathover_of_tr_eq (ap10 (elim_type_glue _ _ a) x)
  begin
    esimp [f_rep_equiv_rep_f],
    exact sorry
  end

  -- set_option pp.universes true
  -- check @elim_type_glue
  -- check @seq_colim
  -- check @seq_diagram
  -- set_option formatter.hide_full_terms false
  -- definition seq_colim_over_glue' (k : ℕ) (p : P (rep k (f a)))
  --   : pathover (seq_colim_over P) (ι' k p) (glue a) (ι' (succ k)
  --                                 (cast ((apo011 P (succ_add n k) (rep_f k a))) p)) :=
-- concato_eq (pathover_of_tr_eq (ap10 (elim_type_glue.{_ _} (λ ⦃n : ℕ⦄ (a : A n), seq_colim.{v} (λ (k : ℕ), P (rep.{l_1} k a))) _ a) (ι' k p))) sorry

--  begin exact sorry
    -- refine concato_eq (pathover_of_tr_eq (ap10 (elim_type_glue.{_ _} (λ ⦃n : ℕ⦄ (a : A n), seq_colim.{v} (λ (k : ℕ), P (rep.{l_1} k a))) _ a) (ι' k p))) sorry,
--    esimp [equiv.trans,equiv.symm,f_rep_equiv_rep_f],
    -- apply ap ι, unfold cast,
    -- rewrite [-my.apo011_inv],
--    exact sorry
--  end

  -- definition seq_colim_over_glue' {k : ℕ} (p : P (rep k (f a)))
  --   : pathover (seq_colim_over P) (ι' k p) (glue a) (shift_down ((to_fun (f_rep_equiv_rep_f a P))⁻¹ (ι' k p))) :=
  -- begin
  --   esimp [f_rep_equiv_rep_f]
  -- end

  definition glue_over (p : P a) : pathover (seq_colim_over P)
    (@ι _ (seq_diagram_of_over P (f a)) 0 (g p)) (glue a) (@ι _ _ 1 (g p)) :=
  !seq_colim_over_glue

  -- set_option class.trace_instances true
  -- set_option pp.all true
  -- attribute rep [reducible]
  -- definition glue_over'' {k : ℕ} (p : P (@rep A f n k a)) : pathover (seq_colim_over P)
  --   (@ι _ (seq_diagram_of_over P (rep k a)) 0 p) _ _ :=
  -- begin
  --   esimp [seq_diagram_of_over],
  --   apply pathover_of_tr_eq,
  --   apply seq_colim_over_glue
  -- end

  -- definition glue_over' {k : ℕ} (p : P (rep k a)) : pathover (seq_colim_over P)
  --   (@ι _ (seq_diagram_of_over P (f a)) 0 p) (glue (rep k a)) (@ι _ _ 1 (g p)) :=
  -- begin
  --   esimp [seq_diagram_of_over],
  --   apply pathover_of_tr_eq,
  --   apply seq_colim_over_glue
  -- end

  -- set_option pp.notation false
  -- set_option pp.implicit true
  definition glue_over_rep (k : ℕ) (p : P (rep k a)) : pathover (seq_colim_over P)
    (@ι _ (seq_diagram_of_over P (rep k a)) 0 p) (rep_glue a k) (@ι _ _ k p) :=
  begin
    revert a p, induction k with k IH, all_goals intro a p,
    { constructor},
    { rewrite [↑seq_diagram_of_over,↑rep_glue,↓rep_glue a k],
      --refine _ ⬝o _,
      unfold ι,
      refine !pathover_tr ⬝o _,
      -- refine eq_concato !glue⁻¹ _, esimp,
      -- refine !glue_over⁻¹ᵒ ⬝o _,
      exact sorry
    }
  end

  -- variables {k l : ℕ} (p : P (rep k a))
  -- check (glue p : ι (g p) = ι p)

  definition sigma_colim_of_colim_sigma (a : seq_colim (λn, Σ(x : A n), P x)) :
    Σ(x : seq_colim A), seq_colim_over P x :=
  begin
  induction a with n v n v,
  { induction v with a p, exact ⟨ι a, @ι _ _ 0 p⟩},
  { induction v with a p, esimp [seq_diagram_sigma], fapply sigma_eq,
      apply glue,
      esimp, exact concato_eq !glue_over (glue p)}
  end

  theorem is_equiv_sigma_colim_of_colim_sigma :
    is_equiv (sigma_colim_of_colim_sigma
      : seq_colim (λn, Σ(x : A n), P x) → Σ(x : seq_colim A), seq_colim_over P x) :=
  begin
    apply is_equiv_of_is_contr_fun,
    intro v,
    induction v with aa pp,
    induction aa,          rotate 1, apply is_hprop.elimo,
    induction pp with k p, rotate 1, apply is_hprop.elimo,
    fapply is_contr.mk,
    { fapply fiber.mk,
      { exact ι ⟨rep k a, p⟩},
      { esimp [sigma_colim_of_colim_sigma], fapply sigma_eq,
        { esimp, apply rep_glue},
        { esimp, rexact glue_over_rep a k p}}},
    { intro v, induction v with v q,
      induction v with l v l v,
      { induction v with a' p', esimp [sigma_colim_of_colim_sigma] at q,
        fapply fiber_eq,
        { esimp, exact sorry},
        { esimp, exact sorry}},
      { induction v with a' p', esimp, exact sorry}}
  end

  variable {P}
  definition colim_sigma_of_sigma_colim (v : Σ(x : seq_colim A), seq_colim_over P x)
    : seq_colim (λn, Σ(x : A n), P x) :=
  begin
    induction v with a p,
    induction a,
    { esimp at p, induction p with k p,
      { exact ι ⟨rep k a, p⟩},
      { apply glue}},
    { esimp, apply arrow_pathover_left, intro x, esimp at x,
      induction x with k p k p,
      { esimp, apply pathover_of_tr_eq, exact sorry},
      { exact sorry}}
  end

  variable (P)
  definition seq_colim_over_equiv [constructor]
    : (Σ(x : seq_colim A), seq_colim_over P x) ≃ seq_colim (λn, Σ(x : A n), P x) :=
  equiv.MK colim_sigma_of_sigma_colim
           sigma_colim_of_colim_sigma
           sorry
           sorry

  end over

end seq_colim
