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

infixr 5 _+_ 

_*_ : Form → Form → Form -- Order
x * n = x
n * m = m
-- m * n = m
m * m = n 

≡-sym : ∀(a b : Form) → a ≡ b → b ≡ a
≡-sym n n = λ x → x
≡-sym n m = λ{ ()}
≡-sym m n = λ{ ()}
≡-sym m m = λ x → x


identity-l : ∀(a : Form) → a ≡ n + a
identity-l n = refl
identity-l m = refl 

identity-r : ∀(a : Form) → a ≡ a + n
identity-r n = refl
identity-r m = refl

+-sym : ∀(a b : Form) → a + b ≡ b + a
+-sym n n = refl
+-sym n m = refl
+-sym m n = refl
+-sym m m = refl

corollary-1 : ∀(a b c : Form) → ((a + b) + c) * m ≡ (a + (b + c)) * m
corollary-1 n n n = refl
corollary-1 n n m = refl
corollary-1 n m n = refl
corollary-1 n m m = refl
corollary-1 m b n = refl
corollary-1 m n m = refl
corollary-1 m m m = refl 

corollary-2 : ∀(a b c : Form) → ((a + b) + c) ≡ (a + b + c)
corollary-2 n n n = refl
corollary-2 n n m = refl
corollary-2 n m n = refl
corollary-2 n m m = refl
corollary-2 m n n = refl
corollary-2 m n m = refl
corollary-2 m m n = refl
corollary-2 m m m = refl

corollary-3 : ∀(a b c : Form) → a + b + c ≡ c + a + b
corollary-3 n n n = refl
corollary-3 n n m = refl
corollary-3 n m n = refl
corollary-3 n m m = refl
corollary-3 m n n = refl
corollary-3 m n m = refl
corollary-3 m m n = refl
corollary-3 m m m = refl

-- * -- Form List for theorems of second order

data +-List ( Form : Set ) : Set₂ where
  <> : +-List Form
  _++_ : Form → +-List Form → +-List Form

infixr 40 _++_