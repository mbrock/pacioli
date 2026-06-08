{-# OPTIONS --safe #-}

module Pacioli where

open import Level using (Level; 0ℓ; _⊔_)
import Algebra.Definitions as Definitions
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (AbelianGroup; CommutativeMonoid; Monoid)
open import Algebra.Structures using (IsAbelianGroup; IsCommutativeMonoid)
import Algebra.Solver.CommutativeMonoid as CMS
import Algebra.Construct.Pointwise as Pointwise
import Data.Nat.Base as Nat
open import Data.Nat.Base using (ℕ; zero)
import Data.Nat.Properties as ℕP
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Fin.Base using (Fin; zero; suc)
import Data.Fin.Properties as FinP
open import Data.Bool.Base using (if_then_else_)
open import Data.Product.Base using (_×_; _,_; proj₂)
import Data.Vec.Base as Vec
open import Data.Vec.Base using ([]; _∷_; tabulate)
open import Relation.Nullary.Decidable.Core using (does)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    ℓᵢ ℓₐ ℓᵣ : Level

record DebitCredit (A : Set ℓₐ) : Set ℓₐ where
  constructor _//_
  field
    debit  : A
    credit : A

open DebitCredit public

Ix : Set ℓᵢ → Set ℓₐ → Set (ℓᵢ ⊔ ℓₐ)
Ix I A = I → A

record CancellativeCommutativeMonoid c ℓ : Set (Level.suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _∙_                   : Op₂ Carrier
    ε                     : Carrier
    isCommutativeMonoid   : IsCommutativeMonoid _≈_ _∙_ ε
    cancel                : Definitions.Cancellative _≈_ _∙_

  open IsCommutativeMonoid isCommutativeMonoid public

  commutativeMonoid : CommutativeMonoid c ℓ
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using
      ( _≉_
      ; rawMagma
      ; magma
      ; semigroup
      ; unitalMagma
      ; rawMonoid
      ; monoid
      ; commutativeMagma
      ; commutativeSemigroup
      )

module Pacioli (M : CancellativeCommutativeMonoid ℓₐ ℓᵣ) where

  open CancellativeCommutativeMonoid M renaming
    ( Carrier to Carrier
    ; _≈_     to _≈ᴬ_
    ; ε       to εᴬ
    ; _∙_     to _∙ᴬ_
    ; cancel  to cancelᴬ
    )
  module S = CMS (CancellativeCommutativeMonoid.commutativeMonoid M)

  cancelʳ : Definitions.RightCancellative _≈ᴬ_ _∙ᴬ_
  cancelʳ = proj₂ cancelᴬ

  infix 4 _≈ᵀ_
  infixl 7 _∙ᵀ_
  infix 8 _⁻¹ᵀ

  _≈ᵀ_ : Rel (DebitCredit Carrier) ℓᵣ
  (a // b) ≈ᵀ (c // d) = (a ∙ᴬ d) ≈ᴬ (c ∙ᴬ b)

  _∙ᵀ_ : Op₂ (DebitCredit Carrier)
  (a // b) ∙ᵀ (c // d) = (a ∙ᴬ c) // (b ∙ᴬ d)

  εᵀ : DebitCredit Carrier
  εᵀ = εᴬ // εᴬ

  _⁻¹ᵀ : Op₁ (DebitCredit Carrier)
  (a // b) ⁻¹ᵀ = b // a

  swap-last : ∀ x y z → (x ∙ᴬ z) ∙ᴬ y ≈ᴬ (x ∙ᴬ y) ∙ᴬ z
  swap-last x y z = let open S; _∙_ = _⊕_ in
    prove 3
      ((var zero ∙ var (suc (suc zero))) ∙ var (suc zero))
      ((var zero ∙ var (suc zero)) ∙ var (suc (suc zero)))
      (x ∷ y ∷ z ∷ [])

  shuffle₄ : ∀ a b c d → (a ∙ᴬ c) ∙ᴬ (b ∙ᴬ d) ≈ᴬ (a ∙ᴬ b) ∙ᴬ (c ∙ᴬ d)
  shuffle₄ a b c d = let open S; _∙_ = _⊕_ in
    prove 4
      ((var zero ∙ var (suc (suc zero))) ∙
       (var (suc zero) ∙ var (suc (suc (suc zero)))))
      ((var zero ∙ var (suc zero)) ∙
       (var (suc (suc zero)) ∙ var (suc (suc (suc zero)))))
      (a ∷ b ∷ c ∷ d ∷ [])

  shuffle₄′ : ∀ a b c d → (a ∙ᴬ b) ∙ᴬ (d ∙ᴬ c) ≈ᴬ (b ∙ᴬ a) ∙ᴬ (c ∙ᴬ d)
  shuffle₄′ a b c d = let open S; _∙_ = _⊕_ in
    prove 4
      ((var zero ∙ var (suc zero)) ∙
       (var (suc (suc (suc zero))) ∙ var (suc (suc zero))))
      ((var (suc zero) ∙ var zero) ∙
       (var (suc (suc zero)) ∙ var (suc (suc (suc zero)))))
      (a ∷ b ∷ c ∷ d ∷ [])

  assocᵀ-lemma :
    ∀ a b c d e f →
    (((a ∙ᴬ c) ∙ᴬ e) ∙ᴬ (b ∙ᴬ (d ∙ᴬ f))) ≈ᴬ
    ((a ∙ᴬ (c ∙ᴬ e)) ∙ᴬ ((b ∙ᴬ d) ∙ᴬ f))
  assocᵀ-lemma a b c d e f = let open S; _∙_ = _⊕_ in
    prove 6
      ((((var zero ∙ var (suc (suc zero))) ∙ var (suc (suc (suc (suc zero))))) ∙
        (var (suc zero) ∙ (var (suc (suc (suc zero))) ∙ var (suc (suc (suc (suc (suc zero)))))))))
      ((var zero ∙ (var (suc (suc zero)) ∙ var (suc (suc (suc (suc zero)))))) ∙
        ((var (suc zero) ∙ var (suc (suc (suc zero)))) ∙ var (suc (suc (suc (suc (suc zero)))))))
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

  idˡᵀ-lemma : ∀ a b → (εᴬ ∙ᴬ a) ∙ᴬ b ≈ᴬ a ∙ᴬ (εᴬ ∙ᴬ b)
  idˡᵀ-lemma a b = let open S; _∙_ = _⊕_ in
    prove 2 ((id ∙ var zero) ∙ var (suc zero))
            (var zero ∙ (id ∙ var (suc zero)))
            (a ∷ b ∷ [])

  idʳᵀ-lemma : ∀ a b → (a ∙ᴬ εᴬ) ∙ᴬ b ≈ᴬ a ∙ᴬ (b ∙ᴬ εᴬ)
  idʳᵀ-lemma a b = let open S; _∙_ = _⊕_ in
    prove 2 ((var zero ∙ id) ∙ var (suc zero))
            (var zero ∙ (var (suc zero) ∙ id))
            (a ∷ b ∷ [])

  invˡᵀ-lemma : ∀ a b → (b ∙ᴬ a) ∙ᴬ εᴬ ≈ᴬ εᴬ ∙ᴬ (a ∙ᴬ b)
  invˡᵀ-lemma a b = let open S; _∙_ = _⊕_ in
    prove 2 ((var (suc zero) ∙ var zero) ∙ id)
            (id ∙ (var zero ∙ var (suc zero)))
            (a ∷ b ∷ [])

  invʳᵀ-lemma : ∀ a b → (a ∙ᴬ b) ∙ᴬ εᴬ ≈ᴬ εᴬ ∙ᴬ (b ∙ᴬ a)
  invʳᵀ-lemma a b = let open S; _∙_ = _⊕_ in
    prove 2 ((var zero ∙ var (suc zero)) ∙ id)
            (id ∙ (var (suc zero) ∙ var zero))
            (a ∷ b ∷ [])

  comm₂ : ∀ a b → a ∙ᴬ b ≈ᴬ b ∙ᴬ a
  comm₂ a b = let open S; _∙_ = _⊕_ in
    prove 2 (var zero ∙ var (suc zero))
            (var (suc zero) ∙ var zero)
            (a ∷ b ∷ [])

  ≈ᵀ-isEquivalence : IsEquivalence _≈ᵀ_
  ≈ᵀ-isEquivalence = record
    { refl = CancellativeCommutativeMonoid.refl M
    ; sym = CancellativeCommutativeMonoid.sym M
    ; trans = λ { {a // b} {c // d} {e // f} p q →
        cancelʳ d _ _
          (CancellativeCommutativeMonoid.trans M
            (swap-last a d f)
            (CancellativeCommutativeMonoid.trans M
              (CancellativeCommutativeMonoid.∙-cong M p (CancellativeCommutativeMonoid.refl M))
              (CancellativeCommutativeMonoid.trans M
                (swap-last c f b)
                (CancellativeCommutativeMonoid.trans M
                  (CancellativeCommutativeMonoid.∙-cong M q (CancellativeCommutativeMonoid.refl M))
                  (swap-last e b d))))) }
    }

  ∙ᵀ-cong : ∀ {x y u v} → x ≈ᵀ y → u ≈ᵀ v → (x ∙ᵀ u) ≈ᵀ (y ∙ᵀ v)
  ∙ᵀ-cong {a // b} {a′ // b′} {c // d} {c′ // d′} p q =
    CancellativeCommutativeMonoid.trans M
      (shuffle₄ a b′ c d′)
      (CancellativeCommutativeMonoid.trans M
        (CancellativeCommutativeMonoid.∙-cong M p q)
        (shuffle₄ a′ c′ b d))

  ∙ᵀ-assoc : ∀ x y z → ((x ∙ᵀ y) ∙ᵀ z) ≈ᵀ (x ∙ᵀ (y ∙ᵀ z))
  ∙ᵀ-assoc (a // b) (c // d) (e // f) = assocᵀ-lemma a b c d e f

  ∙ᵀ-identity : (∀ x → (εᵀ ∙ᵀ x) ≈ᵀ x) × (∀ x → (x ∙ᵀ εᵀ) ≈ᵀ x)
  ∙ᵀ-identity = (λ { (a // b) → idˡᵀ-lemma a b }) , λ { (a // b) → idʳᵀ-lemma a b }

  ⁻¹ᵀ-inverse : (∀ x → ((x ⁻¹ᵀ) ∙ᵀ x) ≈ᵀ εᵀ) × (∀ x → (x ∙ᵀ (x ⁻¹ᵀ)) ≈ᵀ εᵀ)
  ⁻¹ᵀ-inverse = (λ { (a // b) → invˡᵀ-lemma a b }) , λ { (a // b) → invʳᵀ-lemma a b }

  ⁻¹ᵀ-cong : ∀ {x y} → x ≈ᵀ y → (x ⁻¹ᵀ) ≈ᵀ (y ⁻¹ᵀ)
  ⁻¹ᵀ-cong {a // b} {c // d} p =
    CancellativeCommutativeMonoid.trans M
      (comm₂ b c)
      (CancellativeCommutativeMonoid.trans M
        (CancellativeCommutativeMonoid.sym M p)
        (comm₂ a d))

  ∙ᵀ-comm : ∀ x y → (x ∙ᵀ y) ≈ᵀ (y ∙ᵀ x)
  ∙ᵀ-comm (a // b) (c // d) = shuffle₄′ a c b d

  isPacioliGroup : IsAbelianGroup _≈ᵀ_ _∙ᵀ_ εᵀ _⁻¹ᵀ
  isPacioliGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≈ᵀ-isEquivalence
            ; ∙-cong = ∙ᵀ-cong
            }
          ; assoc = ∙ᵀ-assoc
          }
        ; identity = ∙ᵀ-identity
        }
      ; inverse = ⁻¹ᵀ-inverse
      ; ⁻¹-cong = ⁻¹ᵀ-cong
      }
    ; comm = ∙ᵀ-comm
    }

  PacioliGroup : AbelianGroup ℓₐ ℓᵣ
  PacioliGroup = record
    { Carrier = DebitCredit Carrier
    ; _≈_ = _≈ᵀ_
    ; _∙_ = _∙ᵀ_
    ; ε = εᵀ
    ; _⁻¹ = _⁻¹ᵀ
    ; isAbelianGroup = isPacioliGroup
    }

natPointwise : ℕ → CancellativeCommutativeMonoid 0ℓ 0ℓ
natPointwise m = record
  { Carrier = Fin m → ℕ
  ; _≈_ = λ x y → ∀ i → x i ≡ y i
  ; _∙_ = λ x y i → x i Nat.+ y i
  ; ε = λ _ → zero
  ; isCommutativeMonoid =
      CommutativeMonoid.isCommutativeMonoid
        (Pointwise.commutativeMonoid (Fin m) ℕP.+-0-commutativeMonoid)
  ; cancel =
      ( (λ x y z eq i → ℕP.+-cancelˡ-≡ (x i) (y i) (z i) (eq i))
      , (λ x y z eq i → ℕP.+-cancelʳ-≡ (x i) (y i) (z i) (eq i))
      )
  }

module Accounting (m n : ℕ) where

  Amount : Set
  Amount = Fin m → ℕ

  basis : Vec.Vec ℕ m → Amount
  basis = Vec.lookup

  infixl 6 _+_
  _+_ : Amount → Amount → Amount
  (x + y) i = x i Nat.+ y i

  infixl 7 _*_
  _*_ : ℕ → Amount → Amount
  (k * x) i = k Nat.* x i

  Amounts : CancellativeCommutativeMonoid 0ℓ 0ℓ
  Amounts = natPointwise m

  module P = Pacioli Amounts

  T : Set
  T = AbelianGroup.Carrier P.PacioliGroup

  zeroAmount : Amount
  zeroAmount _ = 0

  Zero : T → Set
  Zero (d // c) = ∀ i → d i ≡ c i

  infixl 5 _<>_

  data Tx : Set where
    empty : Tx
    swap  : Amount → Fin n → Fin n → Tx
    _<>_  : Tx → Tx → Tx

  raw : Tx → Fin n → T
  raw empty _ = zeroAmount // zeroAmount
  raw (swap a d c) account =
    (if does (account FinP.≟ d) then a else zeroAmount) //
    (if does (account FinP.≟ c) then a else zeroAmount)
  raw (left <> right) account = raw left account P.∙ᵀ raw right account

  sum : Tx → T
  sum empty = zeroAmount // zeroAmount
  sum (swap a _ _) = a // a
  sum (left <> right) = sum left P.∙ᵀ sum right

  balanced : (tx : Tx) → Zero (sum tx)
  balanced empty _ = refl
  balanced (swap a _ _) _ = refl
  balanced (left <> right) i rewrite balanced left i | balanced right i = refl

module ExampleSystem where

  open Accounting 2 3

  usd eur : Amount
  usd = basis (1 ∷ 0 ∷ [])
  eur = basis (0 ∷ 1 ∷ [])

  cash revenue equity : Fin 3
  cash = zero
  revenue = suc zero
  equity = suc (suc zero)

  cashSale : Tx
  cashSale = swap (10 * usd) revenue cash
