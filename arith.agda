open import Data.Nat
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

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

*-zeroᴿ′ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroᴿ′ zero = refl
*-zeroᴿ′ (suc n) =
  begin
    (suc n) * zero
  ≡⟨⟩
    zero + n * zero
  ≡⟨ *-zeroᴿ′ n ⟩
    zero
  ∎

*-identityᴿ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityᴿ zero = refl
*-identityᴿ (suc n) rewrite *-identityᴿ n = refl

*-simplify : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-simplify zero n = refl
*-simplify (suc m) n rewrite *-simplify m n
                | sym (+-assoc m n (m * n))
                | +-comm m n
                | +-assoc n m (m * n) = refl

*-distrib-+′ : ∀ (n m : ℕ) → (suc n) * m ≡ m + n * m
*-distrib-+′ n m = begin (suc n) * m ≡⟨⟩ m + n * m ∎

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

*-distrib-+″ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+″ zero n p = refl
*-distrib-+″ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+″ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p + m * p + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p
                            | *-assoc m n p = refl

-- prove commutativity of multiplication using rewrite
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroᴿ n = refl
*-comm (suc m) n rewrite *-simplify n m | *-comm m n = refl

-- alternate method using equivalence reasoning rather than rewrite
*-comm′ : ∀ (m n : ℕ) → m * n ≡ n * m
-- base case: 0 * n = n * 0
*-comm′ zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-zeroᴿ n) ⟩
    n * zero
  ∎
-- now prove that (suc m) * n ≡ n * (suc m)
*-comm′ (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong ( n +_ ) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (*-simplify n m) ⟩
    n * (suc m)
  ∎
    
∸-lemma₁ : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-lemma₁ zero = refl
∸-lemma₁ (suc n) = refl

∸-lemma₂ : ∀ (m n : ℕ) → m ∸ suc n ≡ pred (m ∸ n)
∸-lemma₂ m zero = refl
∸-lemma₂ zero (suc n) = refl
∸-lemma₂ (suc m) (suc n) rewrite ∸-lemma₂ m n = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero = 
  begin
    m ∸ n
  ≡⟨ cong (m ∸_) (sym (+-identityᴿ n)) ⟩
    m ∸ (n + zero)
  ∎
∸-+-assoc m n (suc p) = 
  begin
    m ∸ n ∸ suc p
  ≡⟨ (∸-lemma₂ (m ∸ n) p) ⟩
    pred (m ∸ n ∸ p)
  ≡⟨ cong pred (∸-+-assoc m n p) ⟩
    pred (m ∸ (n + p))
  ≡⟨ sym (∸-lemma₂ m (n + p)) ⟩
    m ∸ suc (n + p)
  ≡⟨ cong (m ∸_) (sym (+-suc n p)) ⟩
    m ∸ (n + suc p)
  ∎
