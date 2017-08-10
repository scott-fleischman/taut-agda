module Taut where

-- Example. The tautology function
-- from Programming in Martin-Löf's Type Theory, chapter 14

-- Determines if a boolean expression of n variables
-- (represented as a curried function of n arguments)
-- is a tautology or not.

-- in SASL notation:

-- taut 0 f = f
-- taut n f = taut(n - 1)(f true) and taut(n - 1)(f false)

-- examples:
-- taut 0 : Bool → Bool
-- taut 3 : (Bool → Bool → Bool → Bool) → Bool


data Bool : Set where
  true false : Bool

data N : Set where
  z : N
  succ : N → N
{-# BUILTIN NATURAL N #-}

_∧_ : (x y : Bool) → Bool
true ∧ y = y
false ∧ _ = false

F : N → Set
F z = Bool 
F (succ x) = Bool → F x

taut : (n : N) → F n → Bool
taut z f = f
taut (succ x) f = taut x (f true) ∧ taut x (f false)

-- try using C-c C-d to check the type of `taut 0` and `taut 3` from above
