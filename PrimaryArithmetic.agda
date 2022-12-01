module PrimaryArithmetic where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form


-- ********* PRIMARY ARITHMETIC ********** --

-- * -- Theorem 1. Form
-- The form of any finite cardinal number of crosses
-- can be taken as the form of an expression.

-- * -- Theorem 2. Content
-- If any space pervades an empty cross, 
-- the nalue indicated in the space is the marked state.

content : ∀(x : Form) → x + m ≡ m
content n = refl
content m = refl

-- * -- Theorem 3. Agreement
-- The simplification of an expression is unique.

-- * -- Canon 6. Rule of dominance
-- If an expression e in a space s shows a dominant value in s, 
-- then the value of e is the marked state.
-- Otherwise, the value of e is the unmarked, state.

-- x = m , y = v
-- x * m = y , y * m = x

dominance : ∀(x y : Form) → ¬(y ≡ x) → (x * m ≡ y) → (x ≡ y * m)
dominance = λ{ n m ¬x≡y x*m≡y → refl
             ; m n ¬x≡y x*m≡y → refl}

-- We have shown that the indicators of the two values 
-- in the calculus remain distinct when we take steps towards simplicity,
-- thereby justifying the hypothesis of simplification. 
-- For com­pleteness we must show 
-- that they remain similarly distinct when we take steps away from simplicity.

-- * -- Theorem 4. Distinction ????
-- The value of any expression constructed by taking steps from a given simple expression
-- is distinct from the value of any expres­sion 
-- constructed by taking steps from a different simple expression.
-- ????

-- distinction-+ : ∀(x y s : Form) → ¬(y ≡ x) → ¬(x + s ≡ y + s)
-- distinction-+ = λ{ n n s ¬y≡x x+s≡y+s → ¬y≡x refl
--                  ; n m m ¬y≡x x+s≡y+s → ¬y≡x {!  !}
--                  ; m n m ¬y≡x x+s≡y+s → {!   !}
--                  ; m m s ¬y≡x x+s≡y+s → ¬y≡x refl}



-- * -- Theorem 5. Identity
-- Identical expressions express the same value.

identity : ∀(x : Form) → x ≡ x
identity = λ{ n → refl
            ; m → refl}

-- * -- Theorem 6. Value
-- Expressions of the same value can be identified.

value : ∀(x y z : Form) → (x ≡ z) → (y ≡ z) → (x ≡ y)
value = λ{ n n n x≡z y≡z → refl
         ; m m m x≡z y≡z → refl}


-- * -- Theorem 8. Invariance, called POSITION (Brown 25)
-- If successive spaces sn, sn+i, sn+2 are distinguished by two crosses, 
-- and sn+i pervades an expression identical with the whole expression in sn+i, 
-- then the value of the resultant expression in sn is the unmarked state.

position : ∀(p : Form) → ((((p * m) + p) * m) ≡ n )
position = λ{ n → refl
              ; m → refl}

-- * -- Theorem 9. Variance, called TRANSPOSITION (Brown 26)
-- If successive spaces sn, sn+i, sn+2 are arranged so that sn, sn+i are distinguished by one cross, 
-- and sn+1, sn+2 are distinguished by two crosses (sn+2 being thus in two divisions), 
-- then the whole expression e in sn is equivalent to an expression, similar in other
-- respects to e, in which an identical expression has been taken
-- out of each division of sn+z and put into sn.


transposition : ∀(p q r : Form) → ((((p + r) * m) + ((q + r) * m)) * m) ≡ ((((p * m) + (q * m)) * m) + r)
transposition p q n = 
  begin 
    (((((p + n) * m) + ((q + n) * m)) * m)) 
  ≡⟨⟩ 
    (((((p * m) + (q * m)) * m))) 
  ≡⟨⟩ 
    (((((((p * m) + (q * m)) * m))) + n)) 
  ∎
transposition p q m = 
  begin 
    ((((((p + m) * m) + ((q + m) * m)) * m)) 
  ≡⟨ cong (_* m) (cong ((_+ ((q + m) * m))) (cong (_* m) (content p))) ⟩ 
    ((((m * m) + ((q + m) * m)) * m)) 
  ≡⟨⟩ 
    (((n + ((q + m) * m)) * m)) 
    ≡⟨ cong ((_* m)) (cong (n +_) (cong (_* m) (content q)))⟩
      (((n + (m * m)) * m)) 
    ≡⟨⟩  
      ((((n + n) * m))) 
    ≡⟨⟩
      (n * m)   
    ≡⟨⟩ 
      m 
    ≡⟨ sym (content (((p * m) + (q * m)) * m))⟩ 
     (((((p * m) + (q * m)) * m) + m)) 
    ∎) 
    