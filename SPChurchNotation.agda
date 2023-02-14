module SPChurchNotation where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Relation.Nullary using (¬_)

open import Form 

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- This module will implement a partial translation of SpencerBrown's laws of form into Church notation, based on Turney (1986)
-- We will consider self-referential function as a set of equations including each other as their arguments.


-- Equation

-- data Memory-Equation (Form : Set) : Set₂ where
--     _+_*m : Form → Form → Memory-Equation Form

-- a : Memory-Equation Form
-- a = {!   !} + {!   !} *m
-- -- List of equations

-- data Equation-List (Form : Set₁) : Set₂ where
--     []  : Equation-List (Form → Form → Form)
--     _::_  : (Form → Form → Form) → Equation-List (Form → Form → Form) → Equation-List (Form → Form → Form)

-- infixr 40 _::_

-- Matrix



record MatrixColumn : Set where
  constructor
    ⟨_,_,_,_⟩
  field
    x' : Form
    y' : Form
    a' : Form
    b' : Form


-- compute a column
-- taking in the previous column
-- next values for x and y
-- funtions a and b

computeColumn : MatrixColumn → Form → Form → (Form → Form → Form) → (Form → Form → Form) → MatrixColumn
computeColumn ⟨ x' , y' , a' , b' ⟩ x y a b = ⟨ x , y , a b' x' , b a' y' ⟩


-- (f + a) * m)
a : Form → Form → Form
a a₂ x₁ = (a₂ + x₁) * m

-- (a₁ + x₂) * m
b : Form → Form → Form
b a₁ x₂ = (a₁ + x₂) * m

initColumn : MatrixColumn
initColumn = ⟨ n , n , n , m ⟩

firstColumn = computeColumn initColumn n m a b 

secondColumn = computeColumn firstColumn n m a b 

-- compute the whole matrix base on the 

data MatrixRow (Form : Set) : Set₂ where
    <> : MatrixRow Form
    _::_ : Form → MatrixRow Form → MatrixRow Form


-- adding to MatrixRow - backwards

append : Form → MatrixRow Form → MatrixRow Form 
append form row = form :: row

iterateFormMatrixRow : Form → Nat → MatrixRow Form → MatrixRow Form
iterateFormMatrixRow _ zero row = row
iterateFormMatrixRow form (suc i) row = iterateFormMatrixRow form i (append form row)

xrow : MatrixRow Form
xrow = iterateFormMatrixRow n 5 (iterateFormMatrixRow m 3 (iterateFormMatrixRow n 3 <>))

yrow : MatrixRow Form
yrow = iterateFormMatrixRow n 1 (iterateFormMatrixRow m 3 (iterateFormMatrixRow n 7 <>))


-- compute memory matrix based on rows

data Matrix (MatrixColumn : Set) : Set₂ where
    [] : Matrix MatrixColumn
    _++_ : MatrixColumn → Matrix MatrixColumn → Matrix MatrixColumn

reverseMatrix : Matrix MatrixColumn → Matrix MatrixColumn → Matrix MatrixColumn
reverseMatrix [] revmatrix = revmatrix
reverseMatrix (col ++ initmatrix) [] = reverseMatrix initmatrix (col ++ [])
reverseMatrix (col ++ initmatrix) (revmatrix) = reverseMatrix initmatrix (col ++ revmatrix)

-- take in rows for x and y
-- take in funstions a and b
-- compute a particular matrix column and add it to what has been constructed before

computeMatrix : Matrix MatrixColumn → MatrixRow Form → MatrixRow Form → (Form → Form → Form) → (Form → Form → Form) → Matrix MatrixColumn
-- take the initial column and compute next step
computeMatrix (cinit ++ []) (x :: xrow) (y :: yrow) a b = computeMatrix ((computeColumn cinit x y a b) ++ (cinit ++ [])) xrow yrow a b
computeMatrix (c ++ matrix) (x :: xrow) (y :: yrow) a b = computeMatrix ((computeColumn c x y a b) ++ c ++ matrix) xrow yrow a b
-- when xrow and yrow are exhausted
-- computeMatrix (c ++ matrix) (x :: <>) (y :: <>) a b = (computeColumn c x y a b) ++ (c ++ matrix)
computeMatrix matrix <> _ _ _ = matrix
computeMatrix matrix _ <> _ _ = matrix
-- in case an empty initial matrix is passed
computeMatrix [] (x :: xrow) (y :: yrow) a b = []

memoryMatrix : Matrix MatrixColumn
memoryMatrix = reverseMatrix (computeMatrix (initColumn ++ []) xrow yrow a b) [] 







-- memoryMatrix : Matrix MatrixRow Form
-- memoryMatrix = ? 



-- -- computing functions

-- compute : MatrixRow Form → MatrixRow Form → (Form → Form → Form) → (Form → Form → Form) → Form → Form → Matrix (MatrixRow Form) → Matrix (MatrixRow Form)
-- compute <> _ a₁ a₂ a₁init a₂init matrix = []
-- compute _ <> a₁ a₂ a₁init a₂init matrix = []
-- compute (x₁ :: x₁row) (x₂ :: x₂row) a₁ a₂ a₁prev a₂prev matrix = {!   !} ++ matrix

-- E1 - MEMORY
-- f = ((f + a) * m) + b) * m
-- 
 