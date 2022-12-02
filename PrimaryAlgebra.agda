module PrimaryAlgebra where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryArithmetic using (position; transposition)

-- * -- Consequence 1. Reflexion

reflexion : ∀(a : Form) → (a * m) * m ≡ a
reflexion n = refl
reflexion m = refl

reflexion-algebra : ∀(a : Form) → ((a * m) * m) ≡ a
reflexion-algebra a = 
    begin 
        ((((a * m) * m)) 
    ≡⟨ identity-l ((((a * m) * m))) ⟩ 
        ((n + (((a * m) * m)) )) 
    ≡⟨ cong (( _+ ((a * m) * m) )) (sym (position (a * m))) ⟩ 
        ((((a * m) * m) + (a * m)) * m) + ((a * m) * m) 
    ≡⟨ sym (transposition ((a * m)) a (((a * m) * m))) ⟩ 
        (((((a * m) + ((a * m) * m)) * m) + ((a + ((a * m) * m)) * m)) * m)
    ≡⟨ cong (( _* m )) (cong (_+ ((a + ((a * m) * m)) * m)) (cong (( _* m)) (+-sym ((a * m)) (((a * m) * m))))) ⟩
        ((((((((a * m) * m) + (a * m) ) * m) + (( a + ((a * m) * m) ) * m)) * m)))
    ≡⟨ cong (( _* m)) (cong ((((((a * m) * m) + (a * m) ) * m) +_ )) (cong (( _* m)) (+-sym a (((a * m) * m))))) ⟩ 
        (((((((((a * m) * m) + (a * m) ) * m) + ((((a * m) * m) + a ) * m)) * m)))) 
    ≡⟨ cong (( _* m)) (cong (( _+ ((((a * m) * m) + a ) * m) )) (position ((a * m)))) ⟩ 
        (((n + ((((a * m) * m) + a) * m)) * m)) 
    ≡⟨ cong (( _* m )) (sym (identity-l (((((a * m) * m) + a) * m))))  ⟩ 
        ((((((a * m) * m) + a) * m) * m)) 
    ≡⟨ cong (( _* m)) (identity-r (((((a * m) * m) + a) * m))) ⟩ 
        (((((((a * m) * m) + a) * m) + n) * m)) 
    ≡⟨ cong (( _* m)) (cong (((((a * m) * m) + a) * m) +_) (sym (position a))) ⟩ 
        (((((((a * m) * m) + a) * m) + (((a * m) + a) * m)) * m)) 
    ≡⟨ transposition (((a * m) * m)) ((a * m)) a ⟩ 
        (((((((a * m) * m) * m) + ((a * m) * m)) * m) + a)) 
    ≡⟨ cong (( _+ a)) (position (((a * m) * m))) ⟩ 
        ((n + a)) 
    ≡⟨ sym (identity-l a) ⟩ 
        a ∎)
    

-- * -- Consequence 2. Generation

generation-splitting : ∀(a b : Form) → ((a + b) * m) + b ≡ ((a * m) + b)
generation-splitting n n = refl
generation-splitting n m = refl
generation-splitting m n = refl
generation-splitting m m = refl

generation : ∀(a b : Form) → ((a + b) * m) + b ≡ ((a * m) + b)
generation a b = 
    begin 
        ((((a + b) * m) + b) 
    ≡⟨ cong ((_+ b)) (cong (( _* m)) (cong (( _+ b )) (sym (reflexion a)))) ⟩ 
        (((((((a * m) * m) + b) * m) + b)) 
    ≡⟨ cong (_+ b) (cong (_* m) (cong (((a * m) * m) +_) (sym (reflexion b)))) ⟩ 
        ((((((a * m) * m) + ((b * m) * m)) * m) + b)) 
    ≡⟨ sym (transposition (a * m) (b * m) b) ⟩ 
        (((((((a * m) + b) * m) + (((b * m) + b) * m)) * m)) 
    ≡⟨ cong (_* m) (cong ((((a * m) + b) * m) +_) (position b)) ⟩ 
        ((((((a * m) + b) * m) + n) * m)) 
    ≡⟨  cong (_* m) (sym (identity-r ((((a * m) + b) * m)))) ⟩ 
        ((((((a * m) + b) * m) * m)) 
    ≡⟨ reflexion (((a * m) + b)) ⟩ 
        (((a * m) + b)) 
    ∎))))

-- * -- Consequece 3. Integration

integration-splitting : ∀(a : Form) → (m + a) ≡ m
integration-splitting n = refl
integration-splitting m = refl

integration : ∀(a : Form) → (m + a) ≡ m
integration a = 
    begin 
        (((m + a)) 
    ≡⟨⟩ 
        ((((n * m) + a)) 
    ≡⟨ sym (generation n a) ⟩ 
        ((((n + a) * m) + a)) 
    ≡⟨ sym (reflexion ((((n + a) * m) + a)))  ⟩ 
        ((((((n + a) * m) + a) * m) * m)) 
    ≡⟨ cong (_* m) (cong (_* m) (cong (_+ a) (cong (_* m) (sym (identity-l a  ))) )) ⟩ 
        ((((((a * m) + a) * m) * m)) 
    ≡⟨ cong (_* m) (position a) ⟩ 
        ((n * m)) 
    ≡⟨⟩ 
        m 
    ∎)))