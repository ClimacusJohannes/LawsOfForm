module SecondOrderOperations where

module TheoremsOfTheSecondOrder where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form
open import PrimaryArithmetic
open import PrimaryAlgebra

data ListForm (Form : Set) : Set₁ where
    n⋆ : ListForm Form
    _+'_ : Form → ListForm Form → ListForm Form
    _*'_ : Form → ListForm Form → ListForm Form

infixr 10 _+'_

evaluateListForm : ListForm Form → Form
evaluateListForm n⋆ = n
evaluateListForm (x +' y) = x + evaluateListForm y
evaluateListForm (x *' y) = x * evaluateListForm y

+-commutativityList : ∀(x y : Form) (xs : ListForm Form) → evaluateListForm ( x +' y +' xs ) ≡ evaluateListForm ( y +' x +' xs)
+-commutativityList x y xs = 
  begin 
    evaluateListForm (x +' y +' xs) 
  ≡⟨⟩ 
    (x + (y + evaluateListForm xs)) 
  ≡⟨ sym (corollary-2 x y (evaluateListForm xs) ) ⟩ 
    ((x + y) + evaluateListForm xs)
  ≡⟨ cong (_+ evaluateListForm xs) (+-sym x y) ⟩ 
    (y + x) + evaluateListForm xs 
  ≡⟨ corollary-2 y x (evaluateListForm xs) ⟩ 
    (y + x + evaluateListForm xs) 
  ≡⟨⟩ 
    evaluateListForm (y +' (x +' xs)) 
  ≡⟨⟩
    evaluateListForm (y +' x +' xs) ∎

+-commutativityListAny : ∀ (x y z : Form) (xs : ListForm Form) → evaluateListForm ( x +' y +' z +' xs ) ≡ evaluateListForm ( x +' z +' y +' xs)
+-commutativityListAny x y z xs = 
  begin 
    (evaluateListForm (x +' y +' z +' xs)) 
  ≡⟨⟩ 
    x + evaluateListForm (y +' z +' xs) 
  ≡⟨ cong (x +_) (+-commutativityList y z xs) ⟩ 
    x + evaluateListForm (z +' y +' xs) 
  ≡⟨⟩  
    (evaluateListForm (x +' z +' y +' xs))
  ≡⟨⟩ 
    (evaluateListForm (x +' z +' y +' xs) ∎)
