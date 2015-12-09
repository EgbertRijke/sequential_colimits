/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import types.nat .move_to_lib

open nat eq equiv sigma sigma.ops is_equiv

namespace seq_colim
-- Type sequences are basically presheaves on ⟨ℕ,≤⟩. They form a model of type theory, so we define not only type sequences, but also dependent type sequences and terms thereof.

  definition seq_diagram [class] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)
  -- structure seq_diagram [class] (A : ℕ → Type) : Type :=
  -- (f : Πn, A n → A (succ n))

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  definition is_equiseq [class] {A : ℕ → Type} (f : seq_diagram A) : Type := forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type :=
    (carrier : ℕ → Type)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  definition is_equiv_of_equiseq [instance] {A : ℕ → Type} (f : seq_diagram A) [H : is_equiseq f] : forall (n : ℕ), is_equiv (@f n) :=
    H

  section dependent_sequences

  variable {A : ℕ → Type}
  variable (f : seq_diagram A)

  definition depseq_carrier : Type :=
    forall ⦃n : ℕ⦄, A n → Type

  definition depseq_diagram (P : depseq_carrier) : Type :=
    forall ⦃n : ℕ⦄ ⦃a : A n⦄, P a → P (f a)

  definition tmseq_carrier {P : depseq_carrier} (g : depseq_diagram f P) : Type :=
    forall ⦃n : ℕ⦄ (a : A n), P a

  definition tmseq_diagram {P : depseq_carrier} {g : depseq_diagram f P} (t : @tmseq_carrier _ _ _ g) : Type :=
    forall ⦃n : ℕ⦄ (a : A n), g (t a) = t (f a)

  definition wkseq_carrier (B : ℕ → Type) (g : @seq_diagram B) : @depseq_carrier A :=
    λ n a, B n

  definition wkseq_diagram (B : ℕ → Type) (g : @seq_diagram B) : @depseq_diagram A f (wkseq_carrier B g) :=
    λ n a, (@g n)

  end dependent_sequences

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [instance] [priority 10000] [coercion]

  variables {A : ℕ → Type} [f : seq_diagram A]
  include f

  definition rep0 [reducible] (k : ℕ) : A 0 → A k :=
  begin
    intro a,
    induction k with k x,
    exact a,
    exact f x
  end

  definition  rep0_equiseq_back [H : is_equiseq f] (k : ℕ) : A k → A 0 :=
  begin
    induction k with k IH: intro a,
    exact a,
    exact (IH ((@f k)⁻¹ a)),
  end

  definition rep0_equiseq_is_equiv [instance] [H : is_equiseq f] (k : ℕ) : is_equiv (@rep0 A f k) :=
  begin
    fapply adjointify,
    exact (rep0_equiseq_back k),
    induction k with k IH: intro b,
    exact rfl,
    unfold rep0,
    unfold rep0_equiseq_back,
    fold [rep0 k (rep0_equiseq_back k ((@f k)⁻¹ b))],
    refine _ ⬝ _,
    exact (@f k) ((@f k)⁻¹ b),
    exact (ap (@f k) (IH ((@f k)⁻¹ b))),
    apply right_inv (@f _),
    induction k with k IH: intro b,
    exact rfl,
    unfold rep0_equiseq_back,
    unfold rep0,
    fold [rep0 k b],
    refine _ ⬝ _,
    exact (rep0_equiseq_back k (rep0 k b)),
    exact (ap (rep0_equiseq_back k) (@left_inv _ _ (@f k) _ (rep0 k b))),
    exact IH b,
  end

  section generalized_rep
  variable {n : ℕ}

  definition rep [reducible] (k : ℕ) (a : A n) : A (n + k) :=
  by induction k with k x;exact a;exact f x

  definition rep_f (k : ℕ) (a : A n) : rep k (f a) =[succ_add n k] rep (succ k) a :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  definition  rep_equiseq_back [H : is_equiseq f] (k : ℕ) (a : A (n + k)) : A n :=
  begin
    induction k with k g,
    exact a,
    exact g ((@f (n + k))⁻¹ a),
  end

  definition rep_equiseq_is_equiv [instance] [H : is_equiseq f] (k : ℕ) : is_equiv (λ (a : A n), rep k a) :=
  begin
    fapply adjointify,
    exact (λ (a : A (n + k)), rep_equiseq_back k a),
    induction k with k IH: intro b,
    exact rfl,
    unfold rep,
    unfold rep_equiseq_back,
    fold [rep k (rep_equiseq_back k ((@f (n+k))⁻¹ b))],
    refine _ ⬝ _,
    exact (@f (n+k)) ((@f (n+k))⁻¹ b),
    exact (ap (@f (n+k)) (IH ((@f (n+k))⁻¹ b))),
    apply right_inv (@f _),
    induction k with k IH: intro b,
    exact rfl,
    unfold rep_equiseq_back,
    unfold rep,
    fold [rep k b],
    refine _ ⬝ _,
    exact (rep_equiseq_back k (rep k b)),
    exact (ap (rep_equiseq_back k) (@left_inv _ _ (@f (n+k)) _ (rep k b))),
    exact IH b,
  end

  definition rep_rep (k l : ℕ) (a : A n) : rep k (rep l a) =[nat.add_add n l k] rep (k + l) a :=
  begin
    induction l with l IH,
    { esimp [rep, nat.add_add, add], constructor},
    { rewrite [▸rep k (f (rep l a)) =[ succ_add (n + l) k ⬝ ap succ (nat.add_add n l k)]
                f (rep (k + l) a)],
      refine rep_f k (rep l a) ⬝o _,
      rewrite [▸f (rep k (rep l a)) =[ ap succ (nat.add_add n l k) ] f (rep (k + l) a)],
      apply pathover_ap, exact apo f IH}
  end

  definition f_rep (k : ℕ) (a : A n) : f (rep k a) = rep (succ k) a := idp
  end generalized_rep

  section shift
  variable (A)
  definition shift_diag [instance] [unfold_full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [instance] [unfold_full] [priority 800] (k : ℕ)
    : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [instance] [unfold_full] [priority 800] (k : ℕ)
    : seq_diagram (λn, A (n + k)) :=
  λn a, !succ_add⁻¹ ▸ f a
  end shift

  section constructions

    omit f

    definition constant_seq [instance] (X : Type) :
      seq_diagram (λ n, X) :=
      λ n x, x

    definition arrow_left_diag [instance] [unfold_full] (X : Type) :
      seq_diagram (λn, X → A n) :=
      λn g x, f (g x)

    inductive finset : ℕ → Type :=
      | fin : forall n, finset n → finset (succ n)
      | ftop : forall n, finset (succ n)

    definition seq_finset : seq_diagram finset := finset.fin

    definition id0_seq (x y : A 0) : ℕ → Type :=
      λ n, (@rep0 _ f n x) = (rep0 n y)

    definition id0_seq_diagram (x y : A 0) : seq_diagram (@id0_seq A f x y) :=
      λ (n : ℕ), @ap _ _ (@f n) (rep0 n x) (rep0 n y)

    definition id_seq (n : ℕ) (x y : A n) : ℕ → Type :=
      λ k, (@rep _ f n k x) = (rep k y)

    definition id_seq_diagram (n : ℕ) (x y : A n) : seq_diagram (@id_seq _ f n x y) :=
      λ (k : ℕ), @ap _ _ (@f (n + k)) (rep k x) (rep k y)

  end constructions

  section over

    variable {A}
    variable (P : Π⦃n⦄, A n → Type)

    definition seq_diagram_over [class] : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

    variable [g : seq_diagram_over P]
    include g
    definition seq_diagram_of_over [instance] [unfold_full] {n : ℕ} (a : A n) :
      seq_diagram (λk, P (rep k a)) :=
      λk p, g p

    definition seq_diagram_sigma [instance] : seq_diagram (λn, Σ(x : A n), P x) :=
      λn v, ⟨f v.1, g v.2⟩

    variable {n : ℕ}

    theorem rep_f_equiv [constructor] (a : A n) (k : ℕ) :
      P (rep (succ k) a) ≃ P (rep k (f a)) :=
      equiv_of_eq (apo011 P _ (rep_f k a)⁻¹ᵒ)

    theorem rep_rep_equiv [constructor] (a : A n) (k l : ℕ) :
      P (rep (k + l) a) ≃ P (rep k (rep l a)) :=
      equiv_of_eq (apo011 P _ (rep_rep k l a)⁻¹ᵒ)

  end over

  section sequential_transformations
  /-
    We define the notion of sequential transformation into the type sequence ⟨A,f⟩,
    which is basically a natural transformation of presheaves on ⟨ℕ,≤⟩.
    Another way of looking at sequential transformations is that a sequential transformation from
    ⟨B,g⟩ to ⟨A,f⟩ is a term of the dependent type sequence "⟨A,f⟩ weakened by ⟨B,g⟩" over ⟨B,g⟩.
    A sequential transformation is an equivalence if all its components are.
    We give some very simple examples of sequential transformations,
    including rep0 and the natural map to the shifted sequence.
  -/
    definition seq_trans_carrier {B : ℕ → Type} (g : seq_diagram B) : Type :=
      forall (n : ℕ), B n → A n

    definition seq_trans_natural [class] {B : ℕ → Type} (g : seq_diagram B)
      (t : @seq_trans_carrier A f B g) : Type :=
    forall (n : ℕ) (b : B n), f (t n b) = t (succ n) (g b)

    definition seq_trans_isequiv {B : ℕ → Type} (g : seq_diagram B)
      (t : @seq_trans_carrier _ f _ g) (H : @seq_trans_natural _ _ _ _ t) : Type :=
    forall ⦃n : ℕ⦄, is_equiv (t n)

    definition rep0_into : seq_trans_natural (constant_seq (A 0)) rep0 :=
      begin
      unfold seq_trans_natural,
      intros n a,
      unfold rep0,
      end

    definition rep0_into_equiseq_isequiv (H : is_equiseq f)
      : seq_trans_isequiv (constant_seq (A 0)) rep0 rep0_into :=
    rep0_equiseq_is_equiv

  end sequential_transformations

end seq_colim
