/- stuff I moved here because it was duplicated or not yet fixed -/

import types.nat .sequence

open nat eq equiv sigma sigma.ops is_equiv

/- This was duplicated -/
namespace seq_colim
-- Type sequences are basically presheaves on ⟨ℕ,≤⟩. They form a model of type theory, so we define not only type sequences, but also dependent type sequences and terms thereof.

  definition is_equiv_of_equiseq {A : ℕ → Type} (f : seq_diagram A) [H : is_equiseq f] :
    forall (n : ℕ), is_equiv (@f n) :=
  H

  section dependent_sequences

  variable (A : ℕ → Type)
  variable (f : seq_diagram A)

  definition depseq_carrier [reducible] : Type :=
  forall ⦃n : ℕ⦄, A n → Type

  variable {A}
  definition depseq_diagram [reducible] (P : depseq_carrier A) : Type :=
  forall ⦃n : ℕ⦄ ⦃a : A n⦄, P a → P (f a)

  variable {f}
  definition tmseq_carrier [reducible] {P : depseq_carrier A} (g : depseq_diagram f P) : Type :=
  forall ⦃n : ℕ⦄ (a : A n), P a

  definition tmseq_diagram [reducible] {P : depseq_carrier A} {g : depseq_diagram f P}
    (t : tmseq_carrier g) : Type :=
  forall ⦃n : ℕ⦄ (a : A n), g (t a) = t (f a)

  definition wkseq_carrier (B : ℕ → Type) (g : seq_diagram B) : depseq_carrier A :=
  λ n a, B n

  definition wkseq_diagram (B : ℕ → Type) (g : seq_diagram B) :
    depseq_diagram f (wkseq_carrier B g) :=
  λ n a, (@g n)

  end dependent_sequences

/- this needs some cleanup: order of arguments needs to change, I would make 1 structure with the type of natural transformations. Also, natural transformations are already used in seq_colim, though not with a definition of a natural transformation -/
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
    variables {A : ℕ → Type} (f : seq_diagram A)
    include f
    definition seq_trans_carrier [unfold_full] {B : ℕ → Type} (g : seq_diagram B) : Type :=
    forall (n : ℕ), B n → A n

    definition seq_trans_natural [class] {B : ℕ → Type} (g : seq_diagram B)
      (t : @seq_trans_carrier A f B g) : Type :=
    forall (n : ℕ) (b : B n), f (t n b) = t (succ n) (g b)

    definition seq_trans_isequiv {B : ℕ → Type} (g : seq_diagram B)
      (t : @seq_trans_carrier _ f _ g) (H : @seq_trans_natural _ _ _ _ t) : Type :=
    forall ⦃n : ℕ⦄, is_equiv (t n)

    definition rep0_into : seq_trans_natural f (constant_seq (A 0)) (rep0 f) :=
    begin
      unfold seq_trans_natural,
      intros n a,
      unfold rep0,
    end

    definition rep0_into_equiseq_isequiv (H : is_equiseq f)
      : seq_trans_isequiv f (constant_seq (A 0)) (rep0 f) (rep0_into f) :=
    is_equiv_rep0 f

  end sequential_transformations
end seq_colim
