module TheoremsOfTheSecondOrder where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryArithmetic
open import PrimaryAlgebra

form-from-+-List : +-List Form → Form
form-from-+-List <> = n
form-from-+-List (x ++ xs) = x + (form-from-+-List xs)

transposition-of-+-List : +-List Form → Form → Form
transposition-of-+-List <> r = n * r
transposition-of-+-List (x ++ xs) r = (x * r) + (transposition-of-+-List xs r)

-- * -- Theorem 10

-- theorem10 : ∀ ( list : +-List Form ) → ∀( r : Form ) → ( (( form-from-+-List list ) * m ) * r ) ≡ ((transposition-of-+-List list r ) * m)
-- theorem10 <> n = refl
-- theorem10 <> m = refl
-- theorem10 (x ++ xs) n = 
--   begin 
--     (((x + form-from-+-List xs) * m ) * n)
--   ≡⟨⟩ 
--     {!   !}
-- theorem10 (x ++ xs) m = {!   !} 

theorem10case1 : ∀( r a : Form ) → (((a * m) * m) + r) ≡ (((a + r) * m ) * m )
theorem10case1 r a = 
  begin 
    ((((a * m) * m) + r)) 
  ≡⟨ cong (_+ r) (reflexion a) ⟩ 
    (a + r) 
  ≡⟨ sym (reflexion (a + r)) ⟩ 
    ((((a + r) * m ) * m )) 
  ∎ 

theorem10case2 : ∀( r a b : Form ) → ((((b * m ) + (a * m)) * m) + r) ≡ ((((b + r) * m ) + ((a + r) * m)) * m)
theorem10case2 r a b = 
  begin 
    ((((b * m) + (a * m)) * m) + r) 
  ≡⟨ sym (transposition b a r) ⟩ 
    (((((b + r) * m) + ((a + r) * m)) * m))  
  ∎

theorem10case3+ : ∀( r a b c : Form ) → (( ((( c ) + ( b * m )) + ( a * m )) * m ) * r ) ≡ (((( (((( c * m ) * m) + ( b * m )) * m) * m) + (a * m)) * m) * r)
theorem10case3+ r a b c = 
  begin 
    (((((c + (b * m)) + (a * m)) * m) * r)) 
  ≡⟨ cong (_* r) (cong (_* m) (cong (_+ (a * m)) ( sym (reflexion ((c + (b * m))))))) ⟩ 
    (((((((c + (b * m)) * m) * m) + (a * m)) * m) * r)) 
  ≡⟨ cong (_* r) (cong (_* m) (cong (_+ (a * m)) (cong (_* m) (cong (_* m) (cong (_+ (b * m)) (sym (reflexion c))))))) ⟩ 
    ((((( (((( c * m ) * m) + ( b * m )) * m) * m) + (a * m)) * m) * r)) 
  ∎

theorem10 : ∀( a b c r : Form ) → ( b ≡ (c * m)) → (((b + (a * m)) * m) + r) ≡ ((((c + r) * m) + ((a + r) * m)) * m)
theorem10 a b c r b≡c*m = 
  begin 
    ((((b + (a * m)) * m) + r)) 
  ≡⟨ cong (_+ r) (cong (_* m) (cong (_+ (a * m)) b≡c*m)) ⟩ 
    (((((c * m) + (a * m)) * m) + r)) 
  ≡⟨ cong (_+ r) (cong (_* m) (cong (_+ (a * m)) (sym (reflexion ((c * m)))))) ⟩ 
    (((((((c * m) * m) * m) + (a * m)) * m) + r)) 
  ≡⟨ sym (transposition (((c * m) * m)) a r) ⟩ 
    (((((((c * m) * m) + r) * m) + ((a + r) * m)) * m)) 
  ≡⟨ cong (_* m) (cong (_+ ((a + r) * m)) (cong (_* m) (theorem10case1 r c))) ⟩ 
    (((((((c + r) * m) * m) * m) + ((a + r) * m)) * m)) 
  ≡⟨ cong (_* m) (cong (_+ ((a + r) * m)) (cong (_* m) (reflexion (c + r))) ) ⟩ 
    ((((c + r) * m) + ((a + r) * m)) * m) 
  ∎


-- (d * m ) ­→ (c * r) * m
-- (e * m ) + (d * m) → (e * r) * m + (d * r) * m
