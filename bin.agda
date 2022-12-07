open import Data.Nat
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
open Eq.≡-Reasoning

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

suc-lemma : ∀ (n : ℕ) → suc n ≡ n + 1
suc-lemma zero = refl
suc-lemma (suc n) rewrite suc-lemma n = refl

lemma₀ : ∀ (b : Bin) → from (inc b) ≡ from b + 1
lemma₀ ⟨⟩ = refl
lemma₀ (b O) = refl
lemma₀ (b I) rewrite lemma₀ b
             | sym (+-assoc (from b) (from b) 0)
             
             = {!
          begin
            from b + 1 + (from b + 1 + 0)
          ≡⟨ sym (+-assoc (from b + 1) (from b) (1 + 0)) ⟩
            from b + 1 + from b + 1 + 0
          ≡⟨ cong ((from b) +_) (+-comm 1 (from b)) ⟩
            from b + from b + 1 + 1 + 0
          ≡⟨ cong ((from b + from b + 1) +_) (+-comm 1 0) ⟩
            from b + from b + 1 + 0 + 1
          ≡⟨ cong ((from b + from b) +_) (+-comm 1 (0 + 1)) ⟩
            from b + from b + 0 + 1 + 1
          ∎
!}

lemma₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
lemma₁ ⟨⟩ = refl
lemma₁ (b′ O) = {!!}
lemma₁ (b′ I) = {!!}
