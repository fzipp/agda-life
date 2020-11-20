-- Copyright 2020 Frederik Zipp. All rights reserved.
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file.

module GameOfLife where

open import Data.Bool using (Bool; _∨_; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; zipWith; upTo; sum; map)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)

---- Utility functions ----

mapWithIndex : ∀ {A B : Set} → (A → ℕ → B) → List A → List B
mapWithIndex f xs = zipWith f xs (upTo (length xs))

_element_ : ∀ {A : Set} → List A → ℕ → Maybe A
[] element n = nothing
(x ∷ xs) element 0 = just x
(x ∷ xs) element suc n = xs element n

_-_ : ℕ → ℕ → Maybe ℕ
m - 0 = just m
0 - (suc n) = nothing
suc m - suc n = m - n

catMaybes : ∀ {A : Set} → List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ xs) = catMaybes xs
catMaybes (just x ∷ xs) = x ∷ catMaybes xs

---- Domain ----

data Cell : Set where
  □ : Cell
  ■ : Cell

aliveCount : Cell → ℕ
aliveCount □ = 0
aliveCount ■ = 1

Row : Set
Row = List Cell

Board : Set
Board = List Row

data Pos : Set where
  ⟨_,_⟩ : ℕ → ℕ → Pos

⟨_,_⟩? : Maybe ℕ → Maybe ℕ → Maybe Pos
⟨ just colᵢ , just rowᵢ ⟩? = just ⟨ colᵢ , rowᵢ ⟩
⟨ just colᵢ , nothing   ⟩? = nothing
⟨ nothing   , just rowᵢ ⟩? = nothing
⟨ nothing   , nothing   ⟩? = nothing

neighbourPositions : Pos → List Pos
neighbourPositions ⟨ colᵢ , rowᵢ ⟩ = catMaybes (
  ⟨      (colᵢ - 1) ,      (rowᵢ - 1) ⟩? ∷
  ⟨      (colᵢ - 1) , just (rowᵢ + 0) ⟩? ∷
  ⟨      (colᵢ - 1) , just (rowᵢ + 1) ⟩? ∷
  ⟨ just (colᵢ + 0) ,      (rowᵢ - 1) ⟩? ∷
  ⟨ just (colᵢ + 0) , just (rowᵢ + 1) ⟩? ∷
  ⟨ just (colᵢ + 1) ,      (rowᵢ - 1) ⟩? ∷
  ⟨ just (colᵢ + 1) , just (rowᵢ + 0) ⟩? ∷
  ⟨ just (colᵢ + 1) , just (rowᵢ + 1) ⟩? ∷
  [])

cellAt : Board → Pos → Cell
cellAt board ⟨ colᵢ , rowᵢ ⟩ = fromMaybe □ ((fromMaybe [] (board element rowᵢ)) element colᵢ) 

aliveCountAt : Board → Pos → ℕ
aliveCountAt board pos = aliveCount (cellAt board pos)

neighbourCount : Board → Pos → ℕ
neighbourCount board pos = sum (map (aliveCountAt board) (neighbourPositions pos))

nextCell : Cell → ℕ → Cell
nextCell ■ neighbours = if (neighbours <ᵇ 2) ∨ (3 <ᵇ neighbours) then □ else ■
nextCell □ neighbours = if (neighbours ≡ᵇ 3) then ■ else □

nextRow : Board → Row → ℕ → Row
nextRow board row rowᵢ = mapWithIndex (λ cell colᵢ → nextCell cell (neighbourCount board ⟨ colᵢ , rowᵢ ⟩)) row

nextGen : Board → Board
nextGen board = mapWithIndex (nextRow board) board

nthGen : ℕ → Board → Board
nthGen 0 board = board
nthGen (suc n) board = nextGen (nthGen n board)

---- "Tests" ----

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

-- Glider

gliderBoard : Board
gliderBoard = (
  (□ ∷ ■ ∷ □ ∷ □ ∷ []) ∷
  (□ ∷ □ ∷ ■ ∷ □ ∷ []) ∷
  (■ ∷ ■ ∷ ■ ∷ □ ∷ []) ∷
  (□ ∷ □ ∷ □ ∷ □ ∷ []) ∷
  (□ ∷ □ ∷ □ ∷ □ ∷ []) ∷
  [])

assertGliderGen4 : nthGen 4 gliderBoard ≡ (
  (□ ∷ □ ∷ □ ∷ □ ∷ []) ∷
  (□ ∷ □ ∷ ■ ∷ □ ∷ []) ∷
  (□ ∷ □ ∷ □ ∷ ■ ∷ []) ∷
  (□ ∷ ■ ∷ ■ ∷ ■ ∷ []) ∷
  (□ ∷ □ ∷ □ ∷ □ ∷ []) ∷
  [])
assertGliderGen4 = refl

-- Blinker

blinker_v : Board
blinker_v = (
  (□ ∷ ■ ∷ □ ∷ []) ∷
  (□ ∷ ■ ∷ □ ∷ []) ∷
  (□ ∷ ■ ∷ □ ∷ []) ∷
  [])

blinker_h : Board
blinker_h = (
  (□ ∷ □ ∷ □ ∷ []) ∷
  (■ ∷ ■ ∷ ■ ∷ []) ∷
  (□ ∷ □ ∷ □ ∷ []) ∷
  [])

assertBlinkerGen0 : nthGen 0 blinker_v ≡ blinker_v
assertBlinkerGen0 = refl

assertBlinkerGen1 : nthGen 1 blinker_v ≡ blinker_h
assertBlinkerGen1 = refl

assertBlinkerGen2 : nthGen 2 blinker_v ≡ blinker_v
assertBlinkerGen2 = refl

assertBlinkerGen3 : nthGen 3 blinker_v ≡ blinker_h
assertBlinkerGen3 = refl

gen0-ident : ∀ {b : Board} → nthGen 0 b ≡ b
gen0-ident = refl
