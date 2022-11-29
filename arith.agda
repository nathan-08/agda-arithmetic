open import Data.Nat
open import Relation.Binary.PropositionalEquality

+-assoc : ∀ (m n p : ℕ) → m + n + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identityᴿ : ∀ (n : ℕ) → n + zero ≡ n
+-identityᴿ zero = refl
+-identityᴿ (suc n) rewrite +-identityᴿ n = refl

+-suc : ∀ (m n : ℕ) →  m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityᴿ n = refl
+-comm (suc m) n rewrite +-comm m n | +-suc n m = refl 

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

*-zeroᴿ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroᴿ zero = refl
*-zeroᴿ (suc n) rewrite *-zeroᴿ n = refl

*-identityᴿ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityᴿ zero = refl
*-identityᴿ (suc n) rewrite *-identityᴿ n = refl

*-simplify : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-simplify zero n = refl
*-simplify (suc m) n rewrite *-simplify m n
                | sym (+-assoc m n (m * n))
                | +-comm m n
                | +-assoc n m (m * n) = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero rewrite *-zeroᴿ m | *-zeroᴿ n | *-zeroᴿ (m + n) = refl
*-distrib-+ m n (suc p) rewrite *-simplify (m + n) p
                     | *-simplify m p
                     | *-simplify n p
                     | sym (+-assoc (m + m * p) n (n * p))
                     | +-comm m (m * p)
                     | *-distrib-+ m n p
                     | sym (+-assoc (m + n) (m * p) (n * p))
                     | +-comm (m + n) (m * p)
                     | +-assoc (m * p) m n = refl
