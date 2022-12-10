module ReentryOscillation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}



data Form : Set₁ where
  [] n a : Form
  [_] : Form → Form
  _+_ : Form → Form → Form

{-# NON_TERMINATING #-}
reduce : Form → Form
reduce [] = []
reduce n = n
reduce [ n ] = []
reduce [ [] ] = n
reduce [ x ] = reduce [ (reduce x) ]
reduce ([] + []) = []
reduce ([] + n) = []
reduce (n + []) = []
reduce (x + y) = reduce ((reduce x) + (reduce y))
reduce a = n

-- reduce ( [ [ [ [ [ [ [] + [ [ [ [] + [] ] ] ] ] ] ] ] ] ] )
-- reduce ( [ [ [ [] + [] ] + [] ] + [ [] ] ] + [ [ [ [] ] ] ] )

-- reduce ( [ [ [ [] + [] ] + [] ] + [ [] ] ] )

data Oscillation ( Form : Set₁ ) : Set₂ where
  <> : Oscillation Form
  _::_ : Form → Oscillation Form → Oscillation Form

infixr 40 _::_

data SelfRef ( Form : Set₁) : Set₂ where
  self : Form → SelfRef Form

wrapSelfRef : Form → SelfRef Form
wrapSelfRef x = self x

unwrapSelfRef : SelfRef Form → Form
unwrapSelfRef (self x) = x

reenter : SelfRef Form → SelfRef Form → Form
-- multiplyReentry x _ = unwrapSelfRef x
reenter org (self a) = unwrapSelfRef org
reenter org (self (x + a)) = (reenter org (self x)) + (reenter org (self a))
reenter org (self (a + x)) = (reenter org (self a) ) + (reenter org (self x) )
reenter org (self [ x ]) = [ (reenter org (self x)) ]
reenter org (self (x + y))  = (reenter org (self x) ) + (reenter org (self y) )
reenter org (self x) = n

-- reenter (self ( [ a + [ a ] ] ) ) (self [ a + [ a ] ] )

-- reenter ( (self a) (self a) (suc zero) )

multiplyReentry : SelfRef Form → SelfRef Form → Nat → Oscillation Form
multiplyReentry _ _ zero = <>
multiplyReentry org curr (suc i) = reenter org curr :: (multiplyReentry org (wrapSelfRef (reenter org curr))) i

-- multiplyReentry (self ( [ a + [ a ] ] ) ) (self [ a + [ a ] ] ) 2

evaluateMultiplyReentry : Oscillation Form → Oscillation Form
evaluateMultiplyReentry <> = <>
evaluateMultiplyReentry (x :: xs) = (reduce x) :: (evaluateMultiplyReentry xs)

getOscillation : SelfRef Form → Oscillation Form
getOscillation x = evaluateMultiplyReentry (multiplyReentry x x 16) 

-- getOscillation (self [ a + [ a ] ])

