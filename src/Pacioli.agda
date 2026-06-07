module Pacioli where

open import Data.Nat using (ℕ; zero; suc; _+_)

two : ℕ
two = suc (suc zero)

two-plus-two : ℕ
two-plus-two = two + two
