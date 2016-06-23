/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import types.nat .move_to_lib types.fin

open nat eq equiv sigma sigma.ops is_equiv

  -- MOVE
  definition idontwanttoprovethis (n l k : ℕ) :
    succ_add (n + l) k ⬝ nat.add_assoc n l (succ k) ⬝ ap
    (λ z, n + z)
    (succ_add l k)⁻¹ = nat.add_assoc n (succ l) k :=
  begin
    induction k with k IH,
    { reflexivity},
    { esimp, refine _ ⬝ ap02 succ IH,
      exact sorry}
  end


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

  definition rep0 [reducible] (k : ℕ) : A 0 → A k :=
  begin
    intro a,
    induction k with k x,
      exact a,
      exact f x
  end

  -- definition rep0_back [H : is_equiseq f] (k : ℕ) : A k → A 0 :=
  -- begin
  --   induction k with k IH: intro a,
  --   exact a,
  --   exact (IH ((@f k)⁻¹ a)),
  -- end

  --TODO: make arguments of inv_homotopy_closed explicit
  -- definition is_equiv_rep0 [constructor] [H : is_equiseq f] (k : ℕ) :
  --   is_equiv (rep0 f k) :=
  -- begin
  --   fapply @inv_homotopy_closed,
  --   { exact rep0_back f k},
  --   { induction k with k IH,
  --     { apply is_equiv_id},
  --     { apply is_equiv_compose (@f _) (rep0 f k)}},
  --   { induction k with k IH: intro a,
  --     { reflexivity},
  --     { apply IH}}
  -- end

  definition is_equiv_rep0 [constructor] [H : is_equiseq f] (k : ℕ) :
    is_equiv (rep0 f k) :=
  begin
    induction k with k IH,
    { apply is_equiv_id},
    { apply is_equiv_compose (@f _) (rep0 f k)},
  end

  local attribute is_equiv_rep0 [instance]
  definition rep0_back [reducible] [H : is_equiseq f] (k : ℕ) : A k → A 0 :=
  (rep0 f k)⁻¹

  -- definition is_equiv_rep0 [constructor] [H : is_equiseq f] (k : ℕ) :
  --   is_equiv (rep0 f k) :=
  -- begin
  --   fapply adjointify,
  --   { exact rep0_back f k},
  --   { induction k with k IH: intro b,
  --     { reflexivity},
  --     unfold rep0,
  --     unfold rep0_back,
  --     fold [rep0 f k (rep0_back f k ((@f k)⁻¹ b))],
  --     refine ap (@f k) (IH ((@f k)⁻¹ b)) ⬝ _,
  --     apply right_inv (@f k)},
  --   induction k with k IH: intro b,
  --   exact rfl,
  --   unfold rep0_back,
  --   unfold rep0,
  --   fold [rep0 f k b],
  --   refine _ ⬝ IH b,
  --   exact ap (rep0_back f k) (left_inv (@f k) (rep0 f k b))
  -- end

  section generalized_rep
  variable {n : ℕ}

  definition rep [reducible] (k : ℕ) (a : A n) : A (n + k) :=
  by induction k with k x; exact a; exact f x

  definition rep_f (k : ℕ) (a : A n) : rep f k (f a) =[succ_add n k] rep f (succ k) a :=
  begin
    induction k with k IH,
    { constructor},
    { unfold [succ_add], apply pathover_ap, exact apo f IH}
  end

  definition  rep_back [H : is_equiseq f] (k : ℕ) (a : A (n + k)) : A n :=
  begin
    induction k with k g,
    exact a,
    exact g ((@f (n + k))⁻¹ a),
  end

  definition is_equiv_rep [constructor] [H : is_equiseq f] (k : ℕ) :
    is_equiv (λ (a : A n), rep f k a) :=
  begin
    fapply adjointify,
    { exact rep_back f k},
    { induction k with k IH: intro b,
      { reflexivity},
      unfold rep,
      unfold rep_back,
      fold [rep f k (rep_back f k ((@f (n+k))⁻¹ b))],
      refine ap (@f (n+k)) (IH ((@f (n+k))⁻¹ b)) ⬝ _,
      apply right_inv (@f (n+k))},
    induction k with k IH: intro b,
    exact rfl,
    unfold rep_back,
    unfold rep,
    fold [rep f k b],
    refine _ ⬝ IH b,
    exact ap (rep_back f k) (left_inv (@f (n+k)) (rep f k b))
  end

  definition rep_rep (k l : ℕ) (a : A n) :
    rep f k (rep f l a) =[nat.add_assoc n l k] rep f (l + k) a :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end
print apd
print rep
print pathover_ap
print succ_add
print nat.add_assoc

  -- this should be a squareover
  definition rep_rep_succ (k l : ℕ) (a : A n) :
    rep_rep f k (succ l) a = change_path (idontwanttoprovethis n l k)
    (rep_f f k (rep f l a) ⬝o
     rep_rep f (succ k) l a ⬝o
     pathover_ap _ (λz, n + z) (apd (λz, rep f z a) (succ_add l k)⁻¹ᵖ)) :=
  begin
    induction k with k IH,
    { constructor},
    { exact sorry}
  end


  -- old: don't use
  definition rep_rep' (k l : ℕ) (a : A n) :
    rep f k (rep f l a) =[nat.add_add n l k] rep f (k + l) a :=
  begin
    induction l with l IH,
    { constructor},
    { rewrite [▸rep f k (f (rep f l a)) =[ succ_add (n + l) k ⬝ ap succ (nat.add_add n l k)]
                f (rep f (k + l) a)],
      refine rep_f f k (rep f l a) ⬝o _,
      rewrite [▸f (rep f k (rep f l a)) =[ ap succ (nat.add_add n l k) ] f (rep f (k + l) a)],
      apply pathover_ap, exact apo f IH}
  end

  definition f_rep (k : ℕ) (a : A n) : f (rep f k a) = rep f (succ k) a := idp
  end generalized_rep

  section shift

  definition shift_diag [unfold_full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [unfold_full] (k : ℕ) : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [unfold_full] (k : ℕ) : seq_diagram (λn, A (n + k)) :=
  λn a, transport A (succ_add n k)⁻¹ (f a)
  end shift

  section constructions

    omit f

    definition constant_seq (X : Type) : seq_diagram (λ n, X) :=
    λ n x, x

    definition seq_diagram_arrow_left [unfold_full] (X : Type) : seq_diagram (λn, X → A n) :=
    λn g x, f (g x)

    -- inductive finset : ℕ → Type :=
    -- | fin : forall n, finset n → finset (succ n)
    -- | ftop : forall n, finset (succ n)

    definition seq_diagram_fin : seq_diagram fin :=
    λn, fin.lift_succ

    definition id0_seq (x y : A 0) : ℕ → Type :=
    λ k, rep0 f k x = rep0 f k y

    definition id0_seq_diagram (x y : A 0) : seq_diagram (id0_seq f x y) :=
    λ (k : ℕ) (p : rep0 f k x = rep0 f k y), ap (@f k) p

    definition id_seq (n : ℕ) (x y : A n) : ℕ → Type :=
    λ k, rep f k x = rep f k y

    definition id_seq_diagram (n : ℕ) (x y : A n) : seq_diagram (id_seq f n x y) :=
    λ (k : ℕ) (p : rep f k x = rep f k y), ap (@f (n + k)) p

  end constructions

  section over

    variable {A}
    variable (P : Π⦃n⦄, A n → Type)

    definition seq_diagram_over : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

    variable (g : seq_diagram_over f P)
    variables {f P}

    definition seq_diagram_of_over [unfold_full] {n : ℕ} (a : A n) :
      seq_diagram (λk, P (rep f k a)) :=
    λk p, g p

    definition seq_diagram_sigma [unfold 6] : seq_diagram (λn, Σ(x : A n), P x) :=
    λn v, ⟨f v.1, g v.2⟩

    variables {n : ℕ} (f P)

    theorem rep_f_equiv [constructor] (a : A n) (k : ℕ) :
      P (rep f k (f a)) ≃ P (rep f (succ k) a) :=
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
