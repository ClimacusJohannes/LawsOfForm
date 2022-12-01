module PrimaryAlgebra where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryArithmetic using (position; transposition)

-- * -- Consequence 1. Reflexion

reflexion : ∀(a : Form) → (a * m) * m ≡ a
reflexion a = 
    begin 
        (((a * m) * m)
    ≡⟨⟩ 
        (( n + (((a * m) * m))))
    ≡⟨ cong (( _+ ((a * m) * m) )) (sym (position (a * m))) ⟩ 
        (((( ( ( ((a * m) * m) + (a * m)) * m) + ((a * m) * m))) ))) 
    ≡⟨⟩ 
        ({!   !} 
    ≡⟨⟩ 
        {!   !})