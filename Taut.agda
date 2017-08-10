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

infixr 5 _∧_

F : N → Set
F z = Bool 
F (succ x) = Bool → F x

taut : (n : N) → F n → Bool
taut z f = f
taut (succ x) f = taut x (f true) ∧ taut x (f false)

-- try using C-c C-d to check the type of `taut 0` and `taut 3` from above


-- see below for examples of tautologies

-- other connectives

¬ : Bool → Bool
¬ true = false
¬ false = true

_∨_ : (x y : Bool) → Bool
true ∨ _ = true
false ∨ y = y

_⇒_ : (x y : Bool) → Bool
true ⇒ y = y
false ⇒ _ = true

_⇔_ : (x y : Bool) → Bool
true ⇔ y = y
false ⇔ true = false
false ⇔ false = true


-- equality for proofs
data _≡_ {X : Set} (x : X) : X → Set where
  refl : x ≡ x


-- tautology examples with proofs

excluded-middle : Bool → Bool
excluded-middle A = A ∨ ¬ A

taut-excluded-middle : taut 1 excluded-middle ≡ true
taut-excluded-middle = refl


contraposition : (x y : Bool) → Bool
contraposition A B = (A ⇒ B) ⇔ (¬ B ⇒ ¬ A)

taut-contraposition : taut 2 contraposition ≡ true
taut-contraposition = refl


reductio-ad-absurdum : (x y : Bool) → Bool
reductio-ad-absurdum A B = ((¬ A ⇒ B) ∧ (¬ A ⇒ ¬ B)) ⇒ A

taut-reductio-ad-absurdum : taut 2 reductio-ad-absurdum ≡ true
taut-reductio-ad-absurdum = refl


De-Morgan's-law : (x y : Bool) → Bool
De-Morgan's-law A B = ¬ (A ∧ B) ⇔ (¬ A ∨ ¬ B)

taut-De-Morgan's-law : taut 2 De-Morgan's-law ≡ true
taut-De-Morgan's-law = refl


syllogism : (x y z : Bool) → Bool
syllogism A B C = ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)

taut-syllogism : taut 3 syllogism ≡ true
taut-syllogism = refl


proof-by-cases : (x y z : Bool) → Bool
proof-by-cases A B C = ((A ∨ B) ∧ (A ⇒ C) ∧ (B ⇒ C)) ⇒ C

taut-proof-by-cases : taut 3 proof-by-cases ≡ true
taut-proof-by-cases = refl


curry : (x y z : Bool) → Bool
curry A B C = ((A ∧ B) ⇒ C) ⇔ (A ⇒ (B ⇒ C))

taut-curry : taut 3 curry ≡ true
taut-curry = refl
