
data Id {ℓ} (A : Set ℓ) (x : A) : A → Set ℓ where
  refl : Id A x x

J : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (C : (x y : A) → Id A x y → Set ℓ₂) → 
    ((x : A) → C x x refl) → (m n : A) (p : Id A m n) → C m n p
J A C x m .m refl = x m

sym : (A : Set) (x y : A) → Id A x y → Id A y x
sym A x y x≡y = J A (λ x y _ → Id A y x) (λ _ → refl) x y x≡y


trans : (A : Set) (x y : A) → Id A x y → (z : A) → Id A y z → Id A x z
trans A x y x≡y = J A (λ x y _ → (z : A) → Id A y z → Id A x z) (λ x z z₁ → z₁) x y x≡y

transport : (A B : Set) → Id Set A B → A → B
transport A B A≡B = J Set (λ x y x₁ → x → y) (λ _ x → x) A B A≡B

subst : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : A → Set ℓ₂) (x y : A) → Id A x y → P x → P y
subst A P x y x≡y = J A (λ x₁ y₁ _ → P x₁ → P y₁) (λ x z → z) x y x≡y
