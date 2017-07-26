import cubical.squareover
open eq sigma
/- TODO: move -/
namespace eq

/- move to various places -/
  definition apd02 [unfold 8] {A : Type} {B : A → Type} (f : Πa, B a) {a a' : A} {p q : a = a'}
    (r : p = q) : change_path r (apd f p) = apd f q :=
  by induction r; reflexivity

  definition pathover_ap_cono {A A' : Type} {a₁ a₂ a₃ : A}
    {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} (B' : A' → Type) (f : A → A')
    {b₁ : B' (f a₁)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) :
    pathover_ap B' f (q₁ ⬝o q₂) =
    change_path !ap_con⁻¹ (pathover_ap B' f q₁ ⬝o pathover_ap B' f q₂) :=
  by induction q₁; induction q₂; reflexivity

  definition concato_eq_eq {A : Type} {B : A → Type} {a₁ a₂ : A} {p₁ : a₁ = a₂}
    {b₁ : B a₁} {b₂ b₂' : B a₂} (r : b₁ =[p₁] b₂) (q : b₂ = b₂') :
    r ⬝op q = r ⬝o pathover_idp_of_eq q :=
  by induction q; reflexivity

definition ap_apd0111 {A₁ A₂ A₃ : Type} {B : A₁ → Type} {C : Π⦃a⦄, B a → Type} {a a₂ : A₁}
  {b : B a} {b₂ : B a₂} {c : C b} {c₂ : C b₂}
  (g : A₂ → A₃) (f : Πa b, C b → A₂) (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apd011 C Ha Hb] c₂) :
  ap g (apd0111 f Ha Hb Hc) = apd0111 (λa b c, (g (f a b c))) Ha Hb Hc :=
by induction Hb; induction Hc using idp_rec_on; reflexivity

/- move to squareover -/
section squareover

  variables {A A' : Type} {B : A → Type}
            {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
            {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

            {b : B a}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
            {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/ {q₃₀ : b₂₀ =[p₃₀] b₄₀} /-b₄₀-/
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-t₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-t₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}

  definition move_right_of_top_over {p : a₀₀ = a} {p' : a = a₂₀}
    {s : square p p₁₂ p₀₁ (p' ⬝ p₂₁)} {q : b₀₀ =[p] b} {q' : b =[p'] b₂₀}
    (t : squareover B (move_top_of_right s) (q ⬝o q') q₁₂ q₀₁ q₂₁) :
    squareover B s q q₁₂ q₀₁ (q' ⬝o q₂₁) :=
  begin induction q', induction q, induction q₂₁, exact t end

  /- TODO: replace the version in the library by this -/
  definition hconcato_pathover' {p : a₂₀ = a₂₂} {sp : p = p₂₁} {s : square p₁₀ p₁₂ p₀₁ p}
    {q : b₂₀ =[p] b₂₂} (t₁₁ : squareover B (s ⬝hp sp) q₁₀ q₁₂ q₀₁ q₂₁)
    (r : change_path sp q = q₂₁) : squareover B s q₁₀ q₁₂ q₀₁ q :=
  by induction sp; induction r; exact t₁₁

  variables (s₁₁ q₀₁ q₁₀ q₂₁ q₁₂)
  definition squareover_fill_t : Σ (q : b₀₀ =[p₁₀] b₂₀), squareover B s₁₁ q q₁₂ q₀₁ q₂₁ :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_b : Σ (q : b₀₂ =[p₁₂] b₂₂), squareover B s₁₁ q₁₀ q q₀₁ q₂₁ :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₀ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_l : Σ (q : b₀₀ =[p₀₁] b₀₂), squareover B s₁₁ q₁₀ q₁₂ q q₂₁ :=
  begin
    induction s₁₁, induction q₁₀ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_r : Σ (q : b₂₀ =[p₂₁] b₂₂) , squareover B s₁₁ q₁₀ q₁₂ q₀₁ q :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₁₀ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end


end squareover
end eq
