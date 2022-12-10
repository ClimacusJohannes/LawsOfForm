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

-- constructReentry : SelfRef Form → Form → Nat → Oscillation Form
-- constructReentry x _ zero = unwrapSelfRef x :: <>
-- constructReentry (self []) _ (suc y) = [] :: <>
-- constructReentry (self n) _ (suc y) = n :: <>
-- constructReentry (self a) f (suc y) = f :: constructReentry (self a) (reduce [ f ]) y
-- constructReentry (self [ [] ]) _ (suc y) = n :: <>
-- constructReentry (self [ n ]) _ (suc y) = [] :: <>
-- constructReentry (self [ a ]) _ (suc y) = [ [] ] :: (constructReentry (self [ [ a ] ]) [] y)
-- constructReentry (self [ [ a ] ]) _ (suc y) = {!   !}
-- constructReentry (self [ [ x ] ]) _ (suc y) = {!   !}
-- constructReentry (self [ x + x₁ ]) _ (suc y) = {!   !}
-- constructReentry (self (x + x₁)) _ (suc y) = {!   !}

-- x = constructReentry ((self [ a ])) [] 10

-- self [ [] + y ]
--  if y == n
--    [ [] ] :: <>
--  if y == []
--    [ [] ] :: <>
--  if y == a
--    

-- self [ a ]
-- [] :: n :: <>

-- f = self ( [ a + [ a ] ])
--                    (n)  ([]) 
-- [ a ]            = []  :: n :: <>
-- [ a + [ a ] ]    =  n  :: n :: <>
-- reduce-self-ref ( self ( [ [ a ] + (a + [ [ a ] ] ) ] ) )
-- a = n
-- n
-- a = m
-- n

-- reduce-self-ref (self [ a + y ])
--    reduce-self-ref y = [] :: n :: <>
--    elim-a (reduce-self-ref y) x = for i in reduce-self-ref y reduce i + x

-- self [ x ]
-- x == n
--    self []
-- x == []
--    n :: [] :: <>



-- self-outside ( m )
-- self-outside ( self-inside (m) (n) )

-- _+_ : Form → Form → Form
-- n + b = b
-- m + b = m
-- i + j = m
-- j + i = m
-- i + n = i
-- i + m = m
-- i + i = i
-- j + n = j
-- j + m = m
-- j + j = j

-- data ImgForm : Set where
--   a b : ImgForm




-- sum-f : Form → Form → Form
-- sum-f n y = y
-- sum-f m y = m


-- _+_ : SelfRef Form → SelfRef Form → SelfRef Form -- Number
-- < fst , snd > + < fst₁ , snd₁ > = < (sum-f fst fst₁) , (sum-f snd snd₁) >

-- infixr 5 _+_

-- times : Form → Form → Form -- Order
-- times n y = y
-- times m m = n
-- times m n = m

-- _*_ : SelfRef Form → SelfRef Form → SelfRef Form
-- < fst , snd > * < fst₁ , snd₁ > = < (times fst fst₁) , (times snd snd₁) >



-- self m - najbolj enostavna
-- self n - neobstojeca
-- self ( m * self (m))

-- self ( ((self m) * m) + (self m) )
-- [ ( [] * m ) + [] ]

-- f = [ ( ( ([]  p) * m) + q ) * m) ]  



-- elim-a : Oscillation Form → Form → Oscillation Form
-- elim-a <> _ = <>
-- elim-a (x :: xs) [] = (reduce (x + []) ) :: (elim-a  xs n ) 
-- elim-a (x :: xs) n = (reduce (x + n) ) :: (elim-a xs [])
-- elim-a (x :: xs) a = <>
-- elim-a (x :: xs) [ f ] = <>
-- elim-a (x :: xs) (f + f₁) = <>

-- reduce-self-ref : SelfRef Form → Oscillation Form
-- reduce-self-ref (self []) = [] :: [] :: <>
-- reduce-self-ref (self n) = n :: n :: <>
-- reduce-self-ref (self [ [] ]) = n :: <>
-- reduce-self-ref (self [ n ]) = [] :: <>
-- reduce-self-ref (self [ a ]) = [] :: n :: <>
-- reduce-self-ref (self [ [ x ] ]) = self-invert (reduce-self-ref (self [ x ]))
-- reduce-self-ref (self [ [] + [] ]) = reduce-self-ref (self [ [] ])
-- reduce-self-ref (self [ [] + n ]) = reduce-self-ref (self [ [] ])
-- reduce-self-ref (self [ [] + a ]) = reduce-self-ref (self [ a ])
-- reduce-self-ref (self [ [] + [ y ] ]) = self-invert (reduce-self-ref (self []))
-- reduce-self-ref (self [ [] + (y + y₁) ]) = self-invert (reduce-self-ref (self []))
-- reduce-self-ref (self [ n + y ]) = reduce-self-ref (self [ y ])
-- reduce-self-ref (self [ a + y ]) = self-invert (elim-a (reduce-self-ref (self y)) n)
-- reduce-self-ref (self [ [ x ] + [] ]) = self-invert (reduce-self-ref (self []))
-- reduce-self-ref (self [ [ x ] + n ]) = reduce-self-ref (self [ [ x ] ])
-- reduce-self-ref (self [ [ x ] + a ]) = self-invert (elim-a (reduce-self-ref (self [ x ])) n)
-- reduce-self-ref (self [ [ x ] + [ y ] ]) = self-invert (concat (reduce-self-ref (self [ x ])) (reduce-self-ref (self [ y ])))
-- reduce-self-ref (self [ [ x ] + (y + z) ]) = self-invert (concat (reduce-self-ref (self [ x ])) (concat (reduce-self-ref (self y)) (reduce-self-ref (self z))))
-- reduce-self-ref (self [ (x + y) + z ]) = self-invert (concat (concat (reduce-self-ref (self x)) (reduce-self-ref (self y))) (reduce-self-ref (self [ z ])))
-- reduce-self-ref (self (x + y)) = <>
-- reduce-self-ref (self a) = <>

-- reduceSelfRef : SelfRef Form → Oscillation Form
-- reduceSelfRef (self []) = [] :: <>
-- reduceSelfRef (self n) = n :: <>
-- reduceSelfRef (self a) = <>
-- reduceSelfRef (self [ [] ]) = n :: <>
-- reduceSelfRef (self [ n ]) = [] :: <>
-- reduceSelfRef (self [ a ]) = [] :: (reduceSelfRef {!   !})
-- reduceSelfRef (self [ [ x ] ]) = self-invert (reduceSelfRef (self [ x ]))
-- reduceSelfRef (self [ x + x₁ ]) = {!   !}
-- reduceSelfRef (self (x + x₁)) = {!   !}

-- concat : Oscillation Form →  Oscillation Form → Oscillation Form
-- concat <> <> = <>
-- concat <> x = x
-- concat x <> = x
-- concat (x :: xs) (y :: ys) = (reduce (x + y)) :: (concat xs ys)

-- self-invert : Oscillation Form → Oscillation Form
-- self-invert <> = <>
-- self-invert (x :: y) = reduce [ x ] :: self-invert y