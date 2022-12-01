module Form where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

data Form : Set where
  n m : Form
 
-- 

_+_ : Form → Form → Form -- Number
x + n = x
-- m + n = m
m + m = m
n + x = x

-- 

_*_ : Form → Form → Form -- Order
x * n = x
n * m = m
-- m * n = m
m * m = n 

+-sym : ∀(a b : Form) → a ≡ b → b ≡ a
+-sym n n = λ x → x
+-sym n m = λ{ ()}
+-sym m n = λ{ ()}
+-sym m m = λ x → x