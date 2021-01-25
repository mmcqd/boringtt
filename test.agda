open import Data.Product

record ⊤ : Set where
  constructor <>

data _+_ (A B : Set) : Set where
  inj₁ : A → A + B
  inj₂ : B → A + B

+-Ind : ∀ {A B} {P : A + B → Set} → ((x : A) → P (inj₁ x)) → ((x : B) → P (inj₂ x)) → (x : A + B) → P x
+-Ind l r (inj₁ x) = l x
+-Ind l r (inj₂ x) = r x

Bool : Set
Bool = ⊤ + ⊤
tt : Bool
tt = inj₁ <>
ff : Bool
ff = inj₂ <>

Bool-Ind : ∀ {ℓ} {P : Bool → Set ℓ} → P tt → P ff → (b : Bool) → P b
Bool-Ind t f (inj₁ x) = t
Bool-Ind t f (inj₂ x) = f

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
if inj₁ x then t else f = t
if inj₂ x then t else f = f

_⊎_ : Set → Set → Set
A ⊎ B = Σ Bool λ x → if x then A else B

inj₁' : ∀ {A B} → A → A ⊎ B
inj₁' a = (tt , a)

inj₂' : ∀ {A B} → B → A ⊎ B
inj₂' b = (ff , b)

⊎-Ind : ∀ {A B} {P : A ⊎ B → Set} → ((x : A) → P (inj₁' x)) → ((x : B) → P (inj₂' x)) → (x : A ⊎ B) → P x
⊎-Ind {P = P} l r (x1 , x2) = Bool-Ind (l x2) (r x2) x1
