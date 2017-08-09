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

if_then_else_ : (b t f : Bool) → Bool
if true then t else _ = t
if false then _ else f = f

and : (x y : Bool) → Bool
and x y = if x then y else false

F : N → Set
F z = Bool 
F (succ x) = Bool → Y
  where
  Y = F x

_·_ : {X Y : Set} → (X → Y) → X → Y
x · y = x y

taut : (n : N) → (F n → Bool)
taut z = λ f → f
taut (succ x) = λ f →
  and
    (y · (f · true))
    (y · (f · false))
  where
  y = taut x

-- try using C-c C-d to check the type of `taut 0` and `taut 3` from above
