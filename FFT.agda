open import Algebra

module FFT {c r} (ring : CommutativeRing c r) where

open CommutativeRing ring renaming (Carrier to R; zero to zeroˡʳ)

open import Level using (Level)
open import Data.Product
open import Data.Nat as ℕ using (ℕ; _^_)

private
  variable
    ℓ : Level
    A : Set ℓ
    n : ℕ

-- Uniform pair
twice : Set ℓ → Set ℓ
twice A = A × A

-- Top-down binary leaf trees
infixl 4 _↓_
_↓_ : Set ℓ → ℕ → Set ℓ
_↓_ A ℕ.zero    = A
_↓_ A (ℕ.suc n) = twice (A ↓ n)

-- Bottom-up binary leaf trees
infixl 4 _↑_
_↑_ : Set ℓ → ℕ → Set ℓ
_↑_ A ℕ.zero    = A
_↑_ A (ℕ.suc n) = twice A ↑ n

module List where

  open import Data.List

  -- Evaluation via Horner's rule with a coefficient list.
  horner : List R → R → R
  horner []       x = 0#
  horner (c ∷ cs) x = c + x * horner cs x

  flat↓ : A ↓ n → List A
  flat↓ {n = ℕ.zero}  a = a ∷ []
  flat↓ {n = ℕ.suc n} (as , bs) = flat↓ as ++ flat↓ bs

  -- flat↑ : A ↑ n → List A
  -- flat↑ {n = ℕ.zero}  a = a ∷ []
  -- flat↑ {n = ℕ.suc n} z = {!!}

module Vec where

  open import Data.Vec
  open import Relation.Binary.PropositionalEquality hiding ([_])
  import Data.Nat.Properties as ℕP

  -- Evaluation via Horner's rule with a coefficient vector.
  horner : Vec R n → R → R
  horner []       x = 0#
  horner (c ∷ cs) x = c + x * horner cs x

  flat↓ : A ↓ n → Vec A (2 ^ n)
  flat↓ {n = ℕ.zero}  a = [ a ]
  flat↓ {n = ℕ.suc n} (as , bs) rewrite ℕP.+-identityʳ (2 ^ n) =
    flat↓ as ++ flat↓ bs

-- Goal: Vec A ((2 ^ n) ℕ.+ ℕ.zero)

module Function where

  open import Data.Fin using (Fin; zero; suc)
  open import Function

  -- Evaluation via Horner's rule with a coefficient function.
  horner : (Fin n → R) → R → R
  horner {ℕ.zero } f x = 0#
  horner {ℕ.suc n} f x = f zero + horner (f ∘ suc) x
