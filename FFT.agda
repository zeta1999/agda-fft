open import Algebra

module FFT {c r} (ring : CommutativeRing c r) where

open CommutativeRing ring
  renaming (Carrier to R; zero to zeroˡʳ;
            _+_ to infixl 6 _⊹_ ; _*_ to infixl 7 _·_)

open import Level using (Level)
open import Data.Product using (_×_; _,_)
open import Data.Nat
open import Function

private
  variable
    ℓ : Level
    A : Set ℓ
    m n : ℕ

-- Uniform pair
twice : Set ℓ → Set ℓ
twice A = A × A

-- Top-down binary leaf trees
infixl 4 _↓_
data _↓_ (A : Set ℓ) : ℕ → Set ℓ where
  L↓ : A → A ↓ zero
  B↓ : twice (A ↓ n) → A ↓ suc n

-- Bottom-up binary leaf trees
infixl 4 _↑_
data _↑_ (A : Set ℓ) : ℕ → Set ℓ where
  L↑ : A → A ↑ zero
  B↑ : twice A ↑ n → A ↑ suc n

module List where

  open import Data.List

  -- Evaluation via Horner's rule with a coefficient list.
  horner : List R → R → R
  horner []       x = 0#
  horner (c ∷ cs) x = c ⊹ x · horner cs x

  flat↓ : A ↓ n → List A
  flat↓ (L↓ a) = [ a ]
  flat↓ (B↓ (u , v)) = flat↓ u ++ flat↓ v

  flat↑ : A ↑ n → List A
  flat↑ (L↑ a) = [ a ]
  flat↑ (B↑ t) = concat (map h (flat↑ t))
    where
      h : twice A → List A
      h (a , b) = a ∷ b ∷ []

import Data.Nat.Properties as ℕP

module Vec where

  open import Data.Vec
  open import Relation.Binary.PropositionalEquality hiding ([_])
    renaming (sym to sym≡; refl to refl≡)
  open ≡-Reasoning

  -- Evaluation via Horner's rule with a coefficient vector.
  horner : Vec R n → R → R
  horner []       x = 0#
  horner (c ∷ cs) x = c ⊹ x · horner cs x

  flat↓ : A ↓ n → Vec A (2 ^ n)
  flat↓ (L↓ a) = [ a ]
  flat↓ {n = suc m} (B↓ (u , v)) rewrite ℕP.+-identityʳ (2 ^ m) =
    flat↓ u ++ flat↓ v

  -- Note that 2 * x ≡ x + (x + 0).

  2+2*n : ∀ n → 2 + 2 * n ≡ 2 * suc n
  2+2*n zero = refl≡
  2+2*n (suc n) =
    begin
      2 + 2 * suc n
    ≡⟨⟩
      suc (suc (suc (n + suc (n + zero))))
    ≡⟨ cong (suc ∘ suc) (sym≡ (ℕP.+-suc n (suc (n + zero)))) ⟩
      suc (suc (n + suc (suc (n + zero))))
    ≡⟨⟩
      2 * suc (suc n)
    ∎
  
  flatTwice : Vec (twice A) n → Vec A (2 * n)
  flatTwice [] = []
  flatTwice ((a , b) ∷ z) = subst (Vec _) (2+2*n _) (a ∷ b ∷ flatTwice z)
  
  flat↑ : A ↑ n → Vec A (2 ^ n)
  flat↑ (L↑ a) = [ a ]
  flat↑ (B↑ z) = flatTwice (flat↑ z)

module Fun where

  open import Data.Sum
  open import Data.Fin using (Fin; zero; suc; splitAt)

  -- Evaluation via Horner's rule with a coefficient function.
  horner : (Fin n → R) → R → R
  horner {zero } f x = 0#
  horner {suc n} f x = f zero ⊹ x · horner (f ∘ suc) x

  infixr 5 _++_
  _++_ : (Fin m → A) → (Fin n → A) → (Fin (m + n) → A)
  _++_ {m = m} f g = [ f , g ] ∘ splitAt m

  flat↓ : A ↓ n → Fin (2 ^ n) → A
  flat↓ (L↓ a) = λ { zero → a }
  flat↓ {n = suc m} (B↓ (u , v)) rewrite ℕP.+-identityʳ (2 ^ m) =
    flat↓ u ++ flat↓ v
