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
    
    -- (identity-l {! ((((a * m) * m) + a) * m)
    -- (( _+ ((a + ((a * m) * m)) * m)) * m)   ( cong ( ( _* m) ) (+-sym ((a * m)) (((a * m) * m))) )   