module SecondOrderForm where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryAlgebra
open import PrimaryArithmetic


data SecondOrderForm (Form : Set) : Set₁ where
  n⋆ : SecondOrderForm Form
  _+:_ : Form → SecondOrderForm Form → SecondOrderForm Form
  _+̂_ : SecondOrderForm Form → SecondOrderForm Form → SecondOrderForm Form
  _+:[_]+:_ : SecondOrderForm Form → SecondOrderForm Form → SecondOrderForm Form → SecondOrderForm Form

infixr 15 _+:_
infixr 10 _+:[_]+:_

empty : SecondOrderForm Form
empty = n⋆

singular : SecondOrderForm Form
singular = n +: empty

numberList : SecondOrderForm Form
numberList = m +: singular

orderList : SecondOrderForm Form
orderList = n⋆ +:[ numberList ]+: (m +: n⋆)


evaluateList : SecondOrderForm Form → Form
evaluateList n⋆ = n
evaluateList (x +: xs) = x + (evaluateList xs)
-- evaluateList (x +: (x₁ +: eq)) = x + x₁ + (evaluateList eq)
evaluateList (eq +:[ eq₁ ]+: eq₂) = ((evaluateList eq) + ((evaluateList eq₁) * m)) + (evaluateList eq₂)
-- evaluateList (x +: (eq +:[ eq₁ ]+: eq₂)) = x + (evaluateList ((eq +:[ eq₁ ]+: eq₂)))
-- evaluateList (x +: (x₁ +̂ x₂)) = x + ((evaluateList x₁) + (evaluateList x₂))
evaluateList (x +̂ x₁) = (evaluateList x) + (evaluateList x₁)

-- * -- Theorem 10

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

distributeR : SecondOrderForm Form → SecondOrderForm Form → SecondOrderForm Form
distributeR n⋆ _ = n⋆
distributeR (x +: list) r = n⋆
distributeR (list +̂ list₁) r = n⋆
distributeR (list +:[ list₁ ]+: list₂) r = list +:[ (list₁ +̂ r) ]+: distributeR list₂ r

rewriteListTh10 : SecondOrderForm Form → SecondOrderForm Form
rewriteListTh10 n⋆ = n⋆ +:[ n⋆ +:[ n⋆ ]+: n⋆ ]+: n⋆
rewriteListTh10 (x +: list) = n⋆ +:[ n⋆ +:[ (x +: (rewriteListTh10 list)) ]+: n⋆ ]+: n⋆
rewriteListTh10 (list +̂ list₁) = n⋆ +:[ n⋆ +:[ (list +̂ (rewriteListTh10 list₁)) ]+: n⋆ ]+: n⋆
rewriteListTh10 (list +:[ list₁ ]+: list₂) = n⋆ +:[ n⋆ +:[ (list₁ +̂ (rewriteListTh10 list₂)) ]+: n⋆ ]+: n⋆

example : SecondOrderForm Form
example = n⋆ +:[ m +: n⋆ ]+: (n⋆ +:[ m +: n⋆ ]+: (n⋆ +:[ m +: n⋆ ]+: n⋆))

exampleR : SecondOrderForm Form
exampleR = m +: (n +: n⋆)

evalEq : ∀ (x : Form) (xs : SecondOrderForm Form) → evaluateList (x +: xs) ≡ x + evaluateList (xs)
evalEq = λ x xs → begin 
    evaluateList (x +: xs) 
  ≡⟨⟩ 
    x + (evaluateList xs) 
  ∎

LRidentity : ∀ (list : SecondOrderForm Form) → ((evaluateList (list)) * m) * m ≡ evaluateList ( n⋆ +:[ list ]+: n⋆ ) * m
LRidentity n⋆ = refl
LRidentity (x +: xs) = 
  begin 
    ((evaluateList (x +: xs)) * m) * m
  ≡⟨⟩ 
    (((x + evaluateList (xs)) * m) * m)
  ≡⟨⟩ 
    {!   !} 
LRidentity (list +̂ list₁) = {!   !}
LRidentity (list +:[ list₁ ]+: list₂) = {!   !}

-- theorem10case3+ : ∀( r a b c : Form ) → (( ((( c ) + ( b * m )) + ( a * m )) * m ) * r ) ≡ (((( (((( c * m ) * m) + ( b * m )) * m) * m) + (a * m)) * m) * r)
-- theorem10case3+ r a b c = 
--   begin 
--     (((((c + (b * m)) + (a * m)) * m) * r)) 
--   ≡⟨ cong (_* r) (cong (_* m) (cong (_+ (a * m)) ( sym (reflexion ((c + (b * m))))))) ⟩ 
--     (((((((c + (b * m)) * m) * m) + (a * m)) * m) * r)) 
--   ≡⟨ cong (_* r) (cong (_* m) (cong (_+ (a * m)) (cong (_* m) (cong (_* m) (cong (_+ (b * m)) (sym (reflexion c))))))) ⟩ 
--     ((((( (((( c * m ) * m) + ( b * m )) * m) * m) + (a * m)) * m) * r)) 
--   ∎

-- -- theorem10case3+ : ∀( r a b c : Form ) → (( ((( c ) + ( b * m )) + ( a * m )) * m ) * r ) ≡ (((( (((( c * m ) * m) + ( b * m )) * m) * m) + (a * m)) * m) * r)    a +: r +: n⋆     b +: r +: n⋆    c +: r +: n⋆   +:[ n⋆ ]+: +:[ n⋆ ]+:
-- theorem10case3+ : ∀ ( r a b : Form) (list : SecondOrderForm Form) →  evaluateList ( n⋆ +:[ (( n⋆ +:[ a +: n⋆ ]+: n⋆ +:[ b +: n⋆ ]+: n⋆ ) +̂ ( list +̂ n⋆ ))]+: (r +: n⋆) ) ≡ evaluateList (n⋆ +:[ (n⋆ +:[ a +: r +: n⋆ ]+: n⋆ +:[ b +: r +: n⋆ ]+: n⋆ +:[ r +: list ]+: n⋆) ]+: n⋆)
-- theorem10case3+ r a b n⋆ = {!   !}
-- theorem10case3+ r a b (x +: list) = {!   !}
-- theorem10case3+ r a b (list +̂ list₁) = {!   !}
-- theorem10case3+ r a b (list +:[ list₁ ]+: list₂) = {!   !} 

lemma2 : ∀ (list : SecondOrderForm Form) →  evaluateList (n⋆ +:[ list ]+: n⋆) ≡ (evaluateList list) * m
lemma2 list = 
  begin 
    evaluateList (n⋆ +:[ list ]+: n⋆) 
  ≡⟨⟩ 
    n + ((evaluateList list) * m) + n 
  ≡⟨ sym (identity-l (((evaluateList list) * m) + n)) ⟩ 
    ((evaluateList list * m) + n) 
  ≡⟨ sym (identity-r ((evaluateList list * m))) ⟩ 
    ((evaluateList list) * m) ∎

lemma3 : ∀ (x : Form) (list : SecondOrderForm Form) → x + evaluateList (list) ≡ evaluateList (x +: list)
lemma3 x list = 
  begin 
    x + evaluateList (list) 
  ≡⟨⟩ 
    evaluateList (x +: list) 
  ≡⟨⟩ 
    (evaluateList (x +: list)) 
  ∎

lemma4 : ∀ (list : SecondOrderForm Form) → evaluateList (n⋆ +:[ n⋆ +:[ list ]+: n⋆ ]+: n⋆) ≡ ((evaluateList list) * m) * m
lemma4 list = 
  begin 
    evaluateList (n⋆ +:[ n⋆ +:[ list ]+: n⋆ ]+: n⋆) 
  ≡⟨ lemma2 (n⋆ +:[ list ]+: n⋆) ⟩ 
    (evaluateList (n⋆ +:[ list ]+: n⋆) * m) 
  ≡⟨ cong (_* m) (lemma2 list) ⟩ 
    (((evaluateList list) * m) * m) 
  ∎ 

lemma5 : ∀ (x y : Form) (xs : SecondOrderForm Form) → rewriteListTh10 (x +: y +: xs) ≡ (n⋆ +:[ n⋆ +:[ x +: (n⋆ +:[ n⋆ +:[ y +: (rewriteListTh10 xs) ]+: n⋆ ]+: n⋆) ]+: n⋆ ]+: n⋆)
lemma5 x y xs = 
  begin 
    rewriteListTh10 (x +: y +: xs) 
  ≡⟨⟩ 
    (n⋆ +:[ n⋆ +:[ (x +: (rewriteListTh10 (y +: xs))) ]+: n⋆ ]+: n⋆)  
  ≡⟨⟩ 
    (n⋆ +:[ n⋆ +:[ (x +: (n⋆ +:[ n⋆ +:[ (y +: (rewriteListTh10 (xs))) ]+: n⋆ ]+: n⋆)) ]+: n⋆ ]+: n⋆) 
  ≡⟨⟩ 
    ((n⋆ +:[ n⋆ +:[ (x +: (n⋆ +:[ n⋆ +:[ (y +: (rewriteListTh10 (xs))) ]+: n⋆ ]+: n⋆)) ]+: n⋆ ]+: n⋆)) 
  ∎

lemma1 : ∀ (list : SecondOrderForm Form) → evaluateList ( list ) ≡ evaluateList (rewriteListTh10 list)
lemma1 n⋆ = refl
lemma1 (x +: n⋆) =
  begin 
    x + n
  ≡⟨ cong (x +_) (sym (reflexion n)) ⟩ 
    x + ((n * m) * m) 
  ≡⟨ sym (reflexion (x + ((n * m) * m))) ⟩ 
    (((x + ((n * m) * m)) * m) * m) 
  ≡⟨ cong (_* m) (identity-l (((x + ((n * m) * m)) * m))) ⟩
    ((( n + (x + ((n * m) * m)) * m) * m)) 
  ≡⟨ identity-l (((( n + (x + ((n * m) * m)) * m) * m))) ⟩ 
    (n + ((( n + (x + ((n * m) * m)) * m) * m))) 
  ∎
lemma1 (x +: x₁ +: list) = 
  begin 
    evaluateList (x +: x₁ +: list) 
  ≡⟨⟩ 
    (x + x₁ + (evaluateList list)) 
  ≡⟨ sym (reflexion (x + x₁ + (evaluateList list))) ⟩
    (((x + x₁ + evaluateList list) * m) * m) 
  ≡⟨ cong (_* m) (cong (_* m) (cong (x +_) (sym (reflexion (x₁ + evaluateList list))))) ⟩ 
    (((x + (((x₁ + evaluateList list) * m) * m)) * m) * m) 
  ≡⟨ cong (_* m) (cong (_* m) (cong (x +_) (cong (_* m) (cong (_* m) (cong (x₁ +_) (lemma1 list)))))) ⟩
    ((((x + (((x₁ + evaluateList (rewriteListTh10 list)) * m) * m)) * m) * m))
  ≡⟨ cong (_* m) (cong (_* m) (cong (x +_) (cong (_* m) (cong (_* m) ( lemma3 x₁ (rewriteListTh10 list) ))))) ⟩ 
    ((x + ((evaluateList (x₁ +: rewriteListTh10 list) * m) * m)) * m) * m
  ≡⟨ cong (_* m) (cong (_* m) (cong (x +_) (sym (lemma4 (x₁ +: rewriteListTh10 list))))) ⟩ 
    ((x + evaluateList (n⋆ +:[ n⋆ +:[ x₁ +: rewriteListTh10 list ]+: n⋆ ]+: n⋆)) * m) * m 
  ≡⟨ cong (_* m) (cong (_* m) (lemma3 x (n⋆ +:[ n⋆ +:[ x₁ +: rewriteListTh10 list ]+: n⋆ ]+: n⋆))) ⟩ 
    (((evaluateList (x +: (n⋆ +:[ n⋆ +:[ x₁ +: rewriteListTh10 list ]+: n⋆ ]+: n⋆))) * m) * m) 
  ≡⟨ sym (lemma4 (x +: (n⋆ +:[ n⋆ +:[ x₁ +: rewriteListTh10 list ]+: n⋆ ]+: n⋆)) ) ⟩ 
    evaluateList (n⋆ +:[ n⋆ +:[ x +: (n⋆ +:[ n⋆ +:[ x₁ +: (rewriteListTh10 list) ]+: n⋆ ]+: n⋆) ]+: n⋆ ]+: n⋆) 
  ≡⟨ cong evaluateList (sym (lemma5 x x₁ list)) ⟩ 
    evaluateList (rewriteListTh10 (x +: x₁ +: list)) 
  ∎
lemma1 (x +: (list +̂ list₁)) = {!   !}
lemma1 (x +: (list +:[ list₁ ]+: list₂)) = {!   !}
lemma1 (list +̂ list₁) = {!   !}
lemma1 (list +:[ list₁ ]+: list₂) = {!   !}

theorem10 : ∀ (list r : SecondOrderForm Form) → evaluateList ( n⋆ +:[ list ]+: r ) ≡ evaluateList (n⋆ +:[ (distributeR list r) ]+: n⋆ )
theorem10 n⋆ n⋆ = refl
theorem10 n⋆ (x +: r) = {!   !}
theorem10 n⋆ (r +̂ r₁) = {!   !}
theorem10 n⋆ (r +:[ r₁ ]+: r₂) = {!   !}
theorem10 (x +: list) r = {!   !}
theorem10 (list +̂ list₁) r = {!   !}
theorem10 (list +:[ list₁ ]+: n⋆) r = 
    begin 
        (evaluateList (( n⋆ +:[ list +:[ list₁ ]+: n⋆ ]+: r )) 
    ≡⟨⟩ 
        {!   !} 
    ≡⟨⟩ 
        {!   !})
theorem10 (list +:[ list₁ ]+: list₂) r = {!   !}
    