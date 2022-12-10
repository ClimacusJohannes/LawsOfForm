module PrimaryAlgebra where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryArithmetic using (position; transposition)

-- * -- Consequence 1. Reflexion

reflexion-splitting : ∀(a : Form) → (a * m) * m ≡ a
reflexion-splitting n = refl
reflexion-splitting m = refl

reflexion : ∀(a : Form) → ((a * m) * m) ≡ a
reflexion a = 
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

-- * -- Consequence 4. Occultation

occultation-splitting : ∀(a b : Form) → (((a * m) + b) * m) + a ≡ a
occultation-splitting n n = refl
occultation-splitting n m = refl
occultation-splitting m n = refl
occultation-splitting m m = refl

occultation : ∀(a b : Form) → (((a * m) + b) * m) + a ≡ a
occultation a b = 
  begin 
      (((((a * m) + b) * m) + a) 
  ≡⟨  sym (generation (((a * m) + b)) a) ⟩ 
      (((((((a * m) + b) + a) * m) + a)) 
  ≡⟨ cong (_+ a) (cong (_* m) (cong (_+ a) (sym (generation a b)))) ⟩ 
      (((((((a + b) * m) + b) + a) * m) + a)) 
  ≡⟨ cong (_+ a) (corollary-1 (((a + b) * m)) b a) ⟩ 
      ((((((a + b) * m) + (b + a)) * m) + a)) 
  ≡⟨ cong (_+ a) (cong (_* m) (cong (((a + b) * m) +_) (+-sym b a))) ⟩ 
      ((((((a + b) * m) + (a + b)) * m) + a)) 
  ≡⟨ cong (_+ a) (position (a + b)) ⟩ 
      ((n + a)) 
  ≡⟨ sym (identity-l a) ⟩ 
      a
  ∎))

-- * -- Consequence 5. Iteration

iteration : ∀(a : Form) → a + a ≡ a
iteration a =  
  begin
      ((a + a)
  ≡⟨ cong (_+ a) (sym (reflexion a)) ⟩ 
      (((((a * m) * m) + a))
  ≡⟨ cong (_+ a) (cong (_* m) (identity-r ((a * m)))) ⟩
      (((((a * m) + n) * m) + a)) 
  ≡⟨ occultation a n ⟩ 
      a 
  ∎))

-- * -- Consequence 6. Extension

extension : ∀(a b : Form) → (((a * m) + (b * m)) * m) + (((a * m) + b) * m) ≡ a
extension a b = 
  begin 
      ((((a * m) + (b * m)) * m) + (((a * m) + b) * m)) 
  ≡⟨ sym (reflexion ((((a * m) + (b * m)) * m) + (((a * m) + b) * m))) ⟩ 
      ((((((((a * m) + (b * m)) * m) + (((a * m) + b) * m)) * m) * m))
  ≡⟨ cong (_* m) (cong (_* m) (cong (_+ (((a * m) + b) * m)) (cong (_* m) (+-sym (a * m) (b * m))))) ⟩ 
      ((((((((b * m) + (a * m)) * m) + (((a * m) + b) * m)) * m) * m)) 
  ≡⟨ cong (_* m) (cong (_* m) (cong ((((b * m) + (a * m)) * m) +_) (cong (_* m) (+-sym (a * m) b)) )) ⟩ 
      (((((((b * m) + (a * m)) * m) + ((b + (a * m)) * m)) * m) * m)) 
  ≡⟨ cong ((_* m)) (transposition (b * m) b (a * m)) ⟩ 
      ((((((((b * m) * m) + (b * m)) * m) + (a * m)) * m)) 
  ≡⟨ cong (_* m) (cong (_+ (a * m)) (position (b * m))) ⟩ 
      ((((n + (a * m)) * m)) 
  ≡⟨ cong (_* m) (sym (identity-l (a * m))) ⟩ 
      (((a * m) * m)) 
  ≡⟨ reflexion a ⟩ 
      a 
  ∎))))


-- * -- Consequence 7. Echelon

echelon : ∀(a b c : Form) → ((((a * m) + b) * m) + c ) * m ≡ ((a + c) * m) + (((b * m) + c) * m)
echelon a b c = 
  begin 
      ((((((a * m) + b) * m) + c ) * m) 
  ≡⟨ cong (( _* m)) (cong (_+ c) (cong (_* m) (cong ((a * m) +_) (sym (reflexion b))))) ⟩ 
      (((((((a * m) + ((b * m) * m)) * m) + c) * m)) 
  ≡⟨ cong (_* m) (sym (transposition a ((b * m)) c)) ⟩ 
      (((((((a + c) * m) + (((b * m) + c) * m)) * m) * m)) 
  ≡⟨ reflexion ((((a + c) * m) + (((b * m) + c) * m))) ⟩ 
      (((a + c) * m) + (((b * m) + c) * m)) ∎ )))

-- * -- Consequence 8. Modified transposition

mod-transposition : ∀(a b c r : Form) → (((a * m) + ((b + r) * m) + ((c + r) * m)) * m) ≡ ((((a * m) + (b * m) + (c * m)) * m) + (((a * m) + (r * m)) * m))
mod-transposition a b c r = 
  begin 
      (((((a * m) + ((b + r) * m) + ((c + r) * m)) * m)) 
  ≡⟨ cong (( _* m)) (cong ((a * m) +_) (sym (reflexion ((((b + r) * m) + ((c + r) * m)))))) ⟩ 
      (((((a * m) + (((((b + r) * m) + ((c + r) * m)) * m) * m)) * m)) 
  ≡⟨ cong (_* m) (cong ((a * m) +_) (cong (_* m) (transposition b c r))) ⟩ 
      ((((a * m) + (((((b * m) + (c * m)) * m) + r) * m)) * m)) 
  ≡⟨ cong (_* m) (+-sym ((a * m)) ((((((b * m) + (c * m)) * m) + r) * m))) ⟩ 
      ((((((((b * m) + (c * m)) * m) + r) * m) + (a * m)) * m)) 
  ≡⟨ echelon ((b * m) + (c * m)) r (a * m) ⟩ 
      ((((b * m) + (c * m)) + (a * m)) * m) + (((r * m) + (a * m)) * m) 
  ≡⟨ cong (_+ (((r * m) + (a * m)) * m)) (cong (_* m) (+-sym (((b * m) + (c * m))) (a * m))) ⟩ 
      ((((a * m) + (b * m) + (c * m)) * m) + (((r * m) + (a * m)) * m) 
  ≡⟨ cong ((((a * m) + (b * m) + (c * m)) * m) +_) (cong (_* m) (+-sym (r * m) (a * m))) ⟩ 
      (((a * m) + (b * m) + (c * m)) * m) + (((a * m) + (r * m)) * m) ∎)))

-- * -- Consequence 9. Crosstransposition

crosstransposition : ∀(a b x y r : Form) → ((((b * m) + (r * m)) * m) + (((a * m) + (r * m)) * m) + (((x * m) + r) * m) + (((y * m) + r) * m)) * m ≡ (((r * m) + a + b) * m) + ((r + x + y) * m)
crosstransposition a b x y r = 
  begin 
      ((((((b * m) + (r * m)) * m) +
    (((a * m) + (r * m)) * m) +
    (((x * m) + r) * m) + (((y * m) + r) * m))
    * m)) 
  ≡⟨ cong (_* m) (cong ((((b * m) + (r * m)) * m) +_) (cong ((((a * m) + (r * m)) * m) +_) (sym (reflexion ((((x * m) + r) * m) + (((y * m) + r) * m)))))) ⟩ 
      ((((((b * m) + (r * m)) * m) +
      (((a * m) + (r * m)) * m) +
      ((((((x * m) + r) * m) + (((y * m) + r) * m)) * m) *
      m))
      * m)) 
  ≡⟨ cong (_* m) (cong ((((b * m) + (r * m)) * m) +_) (cong ((((a * m) + (r * m)) * m) +_) (cong (_* m) (transposition (x * m) (y * m) r)))) ⟩ 
    ((((((b * m) + (r * m)) * m) +
      (((a * m) + (r * m)) * m) +
      ((((((x * m) * m) + ((y * m) * m)) * m) + r) * m))
     * m)) 
  ≡⟨ cong (_* m) (cong ((((b * m) + (r * m)) * m) +_) (cong ((((a * m) + (r * m)) * m) +_) (cong (_* m) (cong (_+ r) (cong (_* m) (cong (((x * m) * m) +_) (reflexion y))))))) ⟩ 
    ((((((b * m) + (r * m)) * m) +
      (((a * m) + (r * m)) * m) +
      ((((((x * m) * m) + y) * m) + r) * m))
     * m)) 
  ≡⟨ cong (_* m) (cong ((((b * m) + (r * m)) * m) +_) (cong ((((a * m) + (r * m)) * m) +_) (cong (_* m) (cong (_+ r) (cong (_* m) (cong (_+ y) (reflexion x))))))) ⟩ 
    ((((((b * m) + (r * m)) * m) +
      (((a * m) + (r * m)) * m) + ((((x + y) * m) + r) * m))
     * m)) 
  ≡⟨ cong (_* m) (cong ((((b * m) + (r * m)) * m) +_) (+-sym ((((a * m) + (r * m)) * m)) (((((x + y) * m) + r) * m)))) ⟩ 
    ((((((b * m) + (r * m)) * m) +
      ((((x + y) * m) + r) * m) + (((a * m) + (r * m)) * m))
     * m)) 
  ≡⟨ cong (_* m) (+-sym ((((b * m) + (r * m)) * m)) (((((x + y) * m) + r) * m) + (((a * m) + (r * m)) * m))) ⟩ 
    ((((((((x + y) * m) + r) * m) + (((a * m) + (r * m)) * m)) +
      (((b * m) + (r * m)) * m))
     * m))
  ≡⟨ cong (_* m) (corollary-2 (((((x + y) * m) + r) * m)) ((((a * m) + (r * m)) * m)) ((((b * m) + (r * m)) * m))) ⟩ 
    (((((((((x + y) * m) + r) * m) + (((a * m) + (r * m)) * m) +
      (((b * m) + (r * m)) * m))
     * m)))) 
  ≡⟨ (mod-transposition (((x + y) * m) + r) ((a * m)) ((b * m)) (r * m)) ⟩ 
    (((((((x + y) * m) + r) * m) + ((a * m) * m) + ((b * m) * m)) * m)
    + ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) 
  ≡⟨ cong (_+ ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) (cong (_* m) (+-sym (((((x + y) * m) + r) * m)) (((a * m) * m) + ((b * m) * m)))) ⟩ 
    (((((a * m) * m) + ((b * m) * m)) + ((((x + y) * m) + r) * m)) *
     m)
    + ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m) 
  ≡⟨ cong (_+ ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) (cong (_* m) (cong (_+ ((((x + y) * m) + r) * m)) (cong (_+ ((b * m) * m)) (reflexion a)))) ⟩ 
    ((((a + ((b * m) * m)) + ((((x + y) * m) + r) * m)) * m) +
    ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) 
  ≡⟨ cong (_+ ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) (cong (_* m) (cong (_+ ((((x + y) * m) + r) * m)) (cong (a +_) (reflexion b)))) ⟩ 
    ((((a + b) + ((((x + y) * m) + r) * m)) * m) +
    ((((((x + y) * m) + r) * m) + ((r * m) * m)) * m)) 
  ≡⟨ cong ((((a + b) + ((((x + y) * m) + r) * m)) * m) +_) (cong (_* m) (cong (((((x + y) * m) + r) * m) +_) (reflexion r))) ⟩ 
    (((a + b) + ((((x + y) * m) + r) * m)) * m) +
    ((((((x + y) * m) + r) * m) + r) * m) 
  ≡⟨ cong ((((a + b) + ((((x + y) * m) + r) * m)) * m) +_) (cong (_* m) (generation (((x + y) * m)) r)) ⟩ 
    ((((a + b) + ((((x + y) * m) + r) * m)) * m) +
    (((((x + y) * m) * m) + r) * m)) 
  ≡⟨ cong ((((a + b) + ((((x + y) * m) + r) * m)) * m) +_) (cong (_* m) (cong (_+ r) (reflexion (x + y)))) ⟩
    ((((a + b) + ((((x + y) * m) + r) * m)) * m) + (((x + y) + r) * m))
  ≡⟨ cong ((((a + b) + ((((x + y) * m) + r) * m)) * m) +_) (cong (_* m) (corollary-2 x y r)) ⟩ 
    ((((a + b) + ((((x + y) * m) + r) * m)) * m) + ((x + y + r) * m)) 
  ≡⟨ sym (generation (((a + b) + ((((x + y) * m) + r) * m))) ((x + y + r) * m)) ⟩ 
    ((((a + b) + ((((x + y) * m) + r) * m)) + ((x + y + r) * m)) * m)
    + ((x + y + r) * m) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (corollary-2 ((a + b)) (((((x + y) * m) + r) * m)) (((x + y + r) * m)))) ⟩ 
    ((((a + b) + ((((x + y) * m) + r) * m) + ((x + y + r) * m)) * m) +
    ((x + y + r) * m))
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (+-sym ((((x + y) * m) + r) * m) ((x + y + r) * m)))) ⟩ 
    ((((a + b) + ((x + y + r) * m) + ((((x + y) * m) + r) * m)) * m) +
    ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (((x + y + r) * m) +_) (cong (_* m) (+-sym (((x + y) * m)) r))))) ⟩ 
    ((((a + b) + ((x + y + r) * m) + ((r + ((x + y) * m)) * m)) * m) +
    ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (cong (x +_) (+-sym y r)))))) ⟩ 
    (((a + b) + ((x + r + y) * m) + ((r + ((x + y) * m)) * m)) * m) +
    ((x + y + r) * m) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (sym (corollary-2 x r y)))))) ⟩
    (((a + b) + (((x + r) + y) * m) + ((r + ((x + y) * m)) * m)) * m) +
    ((x + y + r) * m)
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (cong (_+ y) (+-sym x r)))))) ⟩ 
    ((((a + b) + (((r + x) + y) * m) + ((r + ((x + y) * m)) * m)) * m)
    + ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (corollary-2 r x y))))) ⟩ 
    ((((a + b) + ((r + x + y) * m) + ((r + ((x + y) * m)) * m)) * m) +
    ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (cong (_+ x + y) (sym (reflexion r))))))) ⟩ 
    (((a + b) +
      ((((r * m) * m) + x + y) * m) + ((r + ((x + y) * m)) * m))
     * m)
    + ((x + y + r) * m) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (_+ ((r + ((x + y) * m)) * m)) (cong (_* m) (cong (((r * m) * m) +_) (sym (reflexion (x + y)))))))) ⟩ 
    ((((a + b) +
      ((((r * m) * m) + (((x + y) * m) * m)) * m) +
      ((r + ((x + y) * m)) * m))
     * m)
    + ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (cong ((a + b) +_) (cong (((((r * m) * m) + (((x + y) * m) * m)) * m) +_) (cong (_* m) (cong (_+ ((x + y) * m)) (sym (reflexion r)))))) ) ⟩ 
    (((a + b) +
      ((((r * m) * m) + (((x + y) * m) * m)) * m) +
      ((((r * m) * m) + ((x + y) * m)) * m))
     * m)
    + ((x + y + r) * m)
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong ((_* m)) (cong ((a + b) +_) (extension (r * m) ((x + y) * m)))) ⟩  
    ((((a + b) + (r * m)) * m) + ((x + y + r) * m)) 
  ≡⟨ cong (_+ ((x + y + r) * m)) (cong (_* m) (+-sym (a + b) (r * m))) ⟩ 
    ((((r * m) + a + b) * m) + ((x + y + r) * m)) 
  ≡⟨ cong ((((r * m) + a + b) * m) +_) (cong (_* m) (corollary-3 x y r)) ⟩ 
    ((((r * m) + a + b) * m) + ((r + x + y) * m)) 
  ∎ 


