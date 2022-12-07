import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc; *-zeroʳ; *-suc; *-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      -------------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      --------------
    → suc m ≤ suc n

inv-s≤s : ∀ {m n : ℕ}
    → suc m ≤ suc n
      --------------
    → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

infix 4 _≤_
-- reflexivity of ≤
≤-refl : ∀ {n : ℕ}
       ----------
       → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  -------
  → m ≤ p
  
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  --------
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

p₁ : 2 ≤ 4
p₁  = s≤s (s≤s z≤n)

p₂ : 2 ≤ 5
p₂ = s≤s (s≤s z≤n)

+-identityᴿ : ∀ (n : ℕ) → n + 0 ≡ n
+-identityᴿ zero = refl
+-identityᴿ (suc n) =
  begin
    suc n + 0
  ≡⟨ cong (suc) (+-identityᴿ n) ⟩
    suc n
  ∎

-- Here we construct a disjunction type, (m ≤ n OR n ≤ m), which is
-- a proof that either m ≤ n or n ≤ m.
-- Parametrized Type definition
data Total (m n : ℕ) : Set where

  forward :
    m ≤ n
    ---------
   → Total m n

  flipped :
    n ≤ m
    ---------
   → Total m n

-- Indexed Type definition
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ------------
    →  Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ------------
    → Total′ m n


≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero         n = forward z≤n
≤-total (suc m)   zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...     | forward m≤n = forward (s≤s m≤n)
...     | flipped n≤m = flipped (s≤s n≤m)

-- Monotonicity
-- addition monotonic regarding inequality
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    --------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    --------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- multiplication monotonic regarding inequality
*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    ------------
  → m * p ≤ n * p
*-monoˡ-≤ m n zero m≤n rewrite *-zeroʳ m | *-zeroʳ n = z≤n
*-monoˡ-≤ m n (suc p) m≤n rewrite *-suc m p | *-suc n p = 
  +-mono-≤ m n (m * p) (n * p) m≤n (*-monoˡ-≤ m n p m≤n)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ------------
  → n * p ≤ n * q
*-monoʳ-≤ n p q p≤q rewrite *-comm n p | *-comm n q = *-monoˡ-≤ p q n p≤q

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)
