/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import .seq_colim

open nat

namespace seq_colim

  variables {A : ℕ → Type} [f : seq_diagram A]
  variables {n : ℕ} (a : A n)
  include f

  definition arrow_colim_of_colim_arrow {X : Type} (g : seq_colim (λn, X → A n)) (x : X) :
    seq_colim A :=
  begin induction g with n g n g, exact ι (g x), exact glue (g x) end

  definition omega_compact [class] (X : Type) : Type := Π(A : ℕ → Type) [f : seq_diagram A],
  is_equiv (arrow_colim_of_colim_arrow : seq_colim (λn, X → A n) → (X → seq_colim A))


end seq_colim
