{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The Pacioli group and the mathematics of double-entry bookkeeping
--
-- This module formalises the construction behind double-entry
-- bookkeeping (DEB) as described in David Ellerman's "The Mathematics
-- of Double-Entry Bookkeeping" (Mathematics Magazine, 1985) and its
-- vector generalisation ("Double Entry Multidimensional Accounting",
-- 1986).
--
-- Ellerman's central observation: a T-account
--
--     [ debit // credit ]
--
-- is exactly an ordered pair in the *group of differences* of a
-- commutative monoid -- the additive analogue of building the
-- fractions q = num/den out of the whole numbers. The group of
-- differences of the non-negative reals (or, multidimensionally, the
-- non-negative vectors) is what he names the *Pacioli group*, after
-- Luca Pacioli who codified DEB in 1494. The modern relative of this
-- construction is the Grothendieck group; the Pacioli group is its
-- 15th-century special case.
--
-- The construction works for any *cancellative* commutative monoid.
-- Cancellativity is the algebraic content of "you can read a balance
-- off a T-account unambiguously": it is precisely what makes the
-- cross-sum equality below an equivalence relation. We therefore take
-- as input a commutative monoid together with a single left-
-- cancellation witness, and derive everything else.
------------------------------------------------------------------------

module Pacioli where

open import Level using (Level; 0ℓ)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (CommutativeMonoid; AbelianGroup)
open import Algebra.Structures using (IsAbelianGroup)
import Algebra.Definitions as Def
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as ℕ
import Data.Vec.Base as Vec
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.Vec.Properties as Vecₚ
open import Data.Fin.Base using (Fin; zero; suc)
import Data.List.Base as List
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ-syntax)

private
  variable
    c ℓ : Level

------------------------------------------------------------------------
-- T-accounts
--
-- A T-account is an ordered pair written [ debit // credit ]. The name
-- "T-account" comes from the bookkeeper's habit of drawing a T and
-- listing debit entries down the left, credit entries down the right.

record DebitCredit (A : Set c) : Set c where
  constructor _//_
  field
    debit  : A
    credit : A

open DebitCredit public

------------------------------------------------------------------------
-- The Pacioli group of a cancellative commutative monoid
--
-- Given a commutative monoid (Amounts, ∙, ε) in which ∙ is left-
-- cancellative, the T-accounts over it form an abelian group: the
-- group of differences, a.k.a. the Pacioli group.

module Pacioli
  {c ℓ} (CM : CommutativeMonoid c ℓ)  (open CommutativeMonoid CM)
  (∙-cancelˡ : Def.LeftCancellative _≈_ _∙_)
  where

  -- Pull in equational reasoning for the underlying setoid, and the two
  -- stdlib consequences we need: deriving right-cancellation from left-
  -- cancellation + commutativity, and the "middle-four exchange"
  -- (a ∙ c) ∙ (b ∙ d) ≈ (a ∙ b) ∙ (c ∙ d), which is the only shuffling
  -- lemma the group laws really require.
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Algebra.Consequences.Setoid setoid
    using (comm∧cancelˡ⇒cancelʳ; comm∧assoc⇒middleFour)

  ∙-cancelʳ : Def.RightCancellative _≈_ _∙_
  ∙-cancelʳ = comm∧cancelˡ⇒cancelʳ comm ∙-cancelˡ

  middleFour : ∀ a b c d → (a ∙ c) ∙ (b ∙ d) ≈ (a ∙ b) ∙ (c ∙ d)
  middleFour a b c d = comm∧assoc⇒middleFour ∙-cong comm assoc a c b d

  infix  4 _≈ᵀ_
  infixl 6 _∙ᵀ_
  infix  8 _⁻¹ᵀ

  -- Equality of T-accounts is equality of *cross-sums* (Ellerman):
  --   [ a // b ] = [ c // d ]   iff   a + d = c + b.
  -- Two accounts denote the same balance exactly when the debit of one
  -- plus the credit of the other agree both ways round.
  _≈ᵀ_ : Rel (DebitCredit Carrier) ℓ
  (a // b) ≈ᵀ (c // d) = a ∙ d ≈ c ∙ b

  -- Addition of T-accounts: add debits to debits, credits to credits.
  -- This is the *only* operation in the whole system. Posting a journal
  -- to a ledger, recording a transaction -- all of it is this ∙ᵀ.
  _∙ᵀ_ : Op₂ (DebitCredit Carrier)
  (a // b) ∙ᵀ (c // d) = (a ∙ c) // (b ∙ d)

  -- The zero-account [ ε // ε ]. Equations encode as zero-accounts and
  -- valid transactions are additions of (other) zero-accounts; zero
  -- plus zero is zero.
  εᵀ : DebitCredit Carrier
  εᵀ = ε // ε

  -- The additive inverse reverses debit and credit. Negating an account
  -- is just swapping the two sides of the T -- this is what makes a
  -- "credit" the undo of a "debit".
  _⁻¹ᵀ : Op₁ (DebitCredit Carrier)
  (a // b) ⁻¹ᵀ = b // a

  ----------------------------------------------------------------------
  -- The cross-sum relation is an equivalence.
  --
  -- Reflexivity and symmetry are immediate. Transitivity is the one
  -- place cancellation earns its keep: from a∙d ≈ c∙b and c∙f ≈ e∙d we
  -- recover a∙f ≈ e∙b only after cancelling the shared d.

  ≈ᵀ-refl : Reflexive _≈ᵀ_
  ≈ᵀ-refl {a // b} = refl

  ≈ᵀ-sym : Symmetric _≈ᵀ_
  ≈ᵀ-sym {a // b} {c // d} = sym

  -- A small rearrangement used three times below: (a ∙ b) ∙ c ≈ (a ∙ c) ∙ b.
  private
    swap : ∀ a b c → (a ∙ b) ∙ c ≈ (a ∙ c) ∙ b
    swap a b c = begin
      (a ∙ b) ∙ c  ≈⟨ assoc a b c ⟩
      a ∙ (b ∙ c)  ≈⟨ ∙-congˡ (comm b c) ⟩
      a ∙ (c ∙ b)  ≈⟨ assoc a c b ⟨
      (a ∙ c) ∙ b  ∎

  ≈ᵀ-trans : Transitive _≈ᵀ_
  ≈ᵀ-trans {a // b} {c // d} {e // f} ad≈cb cf≈ed =
    ∙-cancelʳ d (a ∙ f) (e ∙ b) (begin
      (a ∙ f) ∙ d  ≈⟨ swap a f d ⟩
      (a ∙ d) ∙ f  ≈⟨ ∙-congʳ ad≈cb ⟩
      (c ∙ b) ∙ f  ≈⟨ swap c b f ⟩
      (c ∙ f) ∙ b  ≈⟨ ∙-congʳ cf≈ed ⟩
      (e ∙ d) ∙ b  ≈⟨ swap e d b ⟩
      (e ∙ b) ∙ d  ∎)

  ≈ᵀ-isEquivalence : IsEquivalence _≈ᵀ_
  ≈ᵀ-isEquivalence = record
    { refl = ≈ᵀ-refl ; sym = ≈ᵀ-sym ; trans = ≈ᵀ-trans }

  ----------------------------------------------------------------------
  -- The group laws.
  --
  -- Each is a short reasoning chain; the middle-four exchange handles
  -- congruence and commutativity, and plain associativity/identity
  -- handle the rest. No solver required.

  ∙ᵀ-cong : ∀ {x y u v} → x ≈ᵀ y → u ≈ᵀ v → (x ∙ᵀ u) ≈ᵀ (y ∙ᵀ v)
  ∙ᵀ-cong {a // b} {a′ // b′} {c // d} {c′ // d′} p q = begin
    (a ∙ c) ∙ (b′ ∙ d′)  ≈⟨ middleFour a b′ c d′ ⟩
    (a ∙ b′) ∙ (c ∙ d′)  ≈⟨ ∙-cong p q ⟩
    (a′ ∙ b) ∙ (c′ ∙ d)  ≈⟨ middleFour a′ c′ b d ⟩
    (a′ ∙ c′) ∙ (b ∙ d)  ∎

  -- Associativity is *not* a commutative shuffle: both components are
  -- reassociated independently, so a single ∙-cong over the two sides
  -- does it.
  ∙ᵀ-assoc : ∀ x y z → ((x ∙ᵀ y) ∙ᵀ z) ≈ᵀ (x ∙ᵀ (y ∙ᵀ z))
  ∙ᵀ-assoc (a // b) (c // d) (e // f) =
    ∙-cong (assoc a c e) (sym (assoc b d f))

  ∙ᵀ-identityˡ : ∀ x → (εᵀ ∙ᵀ x) ≈ᵀ x
  ∙ᵀ-identityˡ (a // b) = begin
    (ε ∙ a) ∙ b  ≈⟨ ∙-congʳ (identityˡ a) ⟩
    a ∙ b        ≈⟨ ∙-congˡ (identityˡ b) ⟨
    a ∙ (ε ∙ b)  ∎

  ∙ᵀ-identityʳ : ∀ x → (x ∙ᵀ εᵀ) ≈ᵀ x
  ∙ᵀ-identityʳ (a // b) = begin
    (a ∙ ε) ∙ b  ≈⟨ ∙-congʳ (identityʳ a) ⟩
    a ∙ b        ≈⟨ ∙-congˡ (identityʳ b) ⟨
    a ∙ (b ∙ ε)  ∎

  -- The double-entry principle in one line: an account and its
  -- debit/credit-reversed inverse sum to the zero-account.
  ∙ᵀ-inverseˡ : ∀ x → ((x ⁻¹ᵀ) ∙ᵀ x) ≈ᵀ εᵀ
  ∙ᵀ-inverseˡ (a // b) = begin
    (b ∙ a) ∙ ε  ≈⟨ identityʳ _ ⟩
    b ∙ a        ≈⟨ comm b a ⟩
    a ∙ b        ≈⟨ identityˡ _ ⟨
    ε ∙ (a ∙ b)  ∎

  ∙ᵀ-inverseʳ : ∀ x → (x ∙ᵀ (x ⁻¹ᵀ)) ≈ᵀ εᵀ
  ∙ᵀ-inverseʳ (a // b) = begin
    (a ∙ b) ∙ ε  ≈⟨ identityʳ _ ⟩
    a ∙ b        ≈⟨ comm a b ⟩
    b ∙ a        ≈⟨ identityˡ _ ⟨
    ε ∙ (b ∙ a)  ∎

  ⁻¹ᵀ-cong : ∀ {x y} → x ≈ᵀ y → (x ⁻¹ᵀ) ≈ᵀ (y ⁻¹ᵀ)
  ⁻¹ᵀ-cong {a // b} {c // d} p = begin
    b ∙ c  ≈⟨ comm b c ⟩
    c ∙ b  ≈⟨ p ⟨
    a ∙ d  ≈⟨ comm a d ⟩
    d ∙ a  ∎

  ∙ᵀ-comm : ∀ x y → (x ∙ᵀ y) ≈ᵀ (y ∙ᵀ x)
  ∙ᵀ-comm (a // b) (c // d) = ∙-cong (comm a c) (comm d b)

  ----------------------------------------------------------------------
  -- Assembling the abelian group.
  --
  -- This is the canonical stdlib shape: a tower of records whose leaves
  -- are the named proofs above, so the structure reads as a table of
  -- contents rather than a wall of inline proofs.

  isPacioliGroup : IsAbelianGroup _≈ᵀ_ _∙ᵀ_ εᵀ _⁻¹ᵀ
  isPacioliGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≈ᵀ-isEquivalence
            ; ∙-cong        = ∙ᵀ-cong
            }
          ; assoc = ∙ᵀ-assoc
          }
        ; identity = ∙ᵀ-identityˡ , ∙ᵀ-identityʳ
        }
      ; inverse = ∙ᵀ-inverseˡ , ∙ᵀ-inverseʳ
      ; ⁻¹-cong = ⁻¹ᵀ-cong
      }
    ; comm = ∙ᵀ-comm
    }

  PacioliGroup : AbelianGroup c ℓ
  PacioliGroup = record { isAbelianGroup = isPacioliGroup }

  -- The canonical inclusion of amounts as debit-balance accounts,
  -- a ↦ [ a // ε ]. This is the unit of the group-of-differences
  -- construction: the universal monoid homomorphism from Amounts into
  -- an abelian group. (Decoding an account [ a // b ] back to a signed
  -- "balance" is then a ∙ᵀ-difference inside this group, i.e. the
  -- debit isomorphism a // b ↦ a − b once a genuine group of values is
  -- in hand. For ℕ-vectors that target group is ℤ-vectors.)
  ι : Carrier → DebitCredit Carrier
  ι a = a // ε

------------------------------------------------------------------------
-- The non-negative n-vectors as a cancellative commutative monoid
--
-- Ellerman's multidimensional accounting: amounts are vectors of
-- incommensurate non-negative quantities (so many dollars, so many
-- euros, so many tonnes of steel), added componentwise. ℕ is a
-- cancellative commutative monoid under +, and that property is
-- inherited componentwise by Vec.

module NonNegativeVectors (m : ℕ) where

  Amount : Set
  Amount = Vec ℕ m

  infixl 6 _+_
  _+_ : Op₂ Amount
  _+_ = Vec.zipWith ℕ._+_

  -- Vec-of-(commutative monoid) is a commutative monoid, built from the
  -- componentwise lifting lemmas in Data.Vec.Properties.
  Amounts : CommutativeMonoid 0ℓ 0ℓ
  Amounts = record
    { Carrier = Amount
    ; _≈_ = _≡_
    ; _∙_ = _+_
    ; ε   = Vec.replicate m 0
    ; isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = record { refl = ≡-refl ; sym = ≡-sym ; trans = ≡-trans }
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = Vecₚ.zipWith-assoc ℕ.+-assoc
            }
          ; identity = Vecₚ.zipWith-identityˡ ℕ.+-identityˡ
                     , Vecₚ.zipWith-identityʳ ℕ.+-identityʳ
          }
        ; comm = Vecₚ.zipWith-comm ℕ.+-comm
        }
    }

  -- Left-cancellation, componentwise. Right-cancellation is then free
  -- inside the Pacioli construction (derived from this + commutativity),
  -- so we never write it out.
  +-cancelˡ′ : ∀ {m} → Def.LeftCancellative (_≡_ {A = Vec ℕ m}) (Vec.zipWith ℕ._+_)
  +-cancelˡ′ []       []       []       _  = ≡-refl
  +-cancelˡ′ (x ∷ xs) (y ∷ ys) (z ∷ zs) eq =
    cong₂ _∷_ (ℕ.+-cancelˡ-≡ x y z (cong Vec.head eq))
              (+-cancelˡ′ xs ys zs (cong Vec.tail eq))

  +-cancelˡ : Def.LeftCancellative _≡_ _+_
  +-cancelˡ = +-cancelˡ′

  -- NOTE on representation. Using Data.Vec keeps amount literals
  -- readable as `1 ∷ 0 ∷ []`, which matters for worked examples. If you
  -- prefer the algebra to fall out for free, switch Amount to
  -- Data.Vec.Functional (= Fin m → ℕ) and replace this whole record
  -- with `Algebra.Construct.Pointwise.commutativeMonoid ℕ.+-0-commutativeMonoid`,
  -- supplying only a one-line pointwise cancellation proof.

------------------------------------------------------------------------
-- Accounting: ledgers, journals, transactions and the trial balance
--
-- Now the bookkeeping vocabulary lines up with the algebra:
--   * a ledger / equation       = a list of T-accounts summing to εᵀ
--   * a transaction             = a balanced list of T-accounts
--   * the trial balance         = the proof that a list sums to εᵀ
--   * posting journal to ledger = appending lists (and the sums add)

module Accounting (m n : ℕ) where

  open NonNegativeVectors m using (Amounts; +-cancelˡ)
    renaming (_+_ to _+ᴬ_)
  open CommutativeMonoid Amounts using () renaming (ε to 𝟘)

  Amount : Set
  Amount = NonNegativeVectors.Amount m

  -- The Pacioli group of T-accounts over these amounts. We work inside
  -- it directly, so ∙ᵀ, εᵀ, the group laws and its equational reasoning
  -- are all in scope under their group names.
  module P = Pacioli Amounts +-cancelˡ
  open AbelianGroup P.PacioliGroup
    renaming (Carrier to T; _≈_ to _≈ᵀ_; _∙_ to _∙ᵀ_; ε to εᵀ; _⁻¹ to _⁻¹ᵀ)
  open import Relation.Binary.Reasoning.Setoid setoid

  -- n named accounts (Assets, Liabilities, Equity, ...), each carrying a
  -- T-account value.
  Posting : Set
  Posting = Fin n × T

  RawTx : Set
  RawTx = List Posting

  -- The sum of a list of postings' T-accounts. This single fold is
  -- "take the trial balance".
  total : RawTx → T
  total = List.foldr (λ p acc → proj₂ p ∙ᵀ acc) εᵀ

  -- A list balances when its postings sum to the zero-account. This is
  -- exactly the double-entry principle / a valid trial balance.
  Balanced : RawTx → Set
  Balanced raw = total raw ≈ᵀ εᵀ

  -- A transaction is a list of postings together with a proof it
  -- balances.
  Tx : Set
  Tx = Σ[ raw ∈ RawTx ] Balanced raw

  postings : Tx → RawTx
  postings = proj₁

  -- The empty transaction balances trivially (εᵀ ≈ᵀ εᵀ).
  empty : Tx
  empty = [] , refl

  -- total is a monoid homomorphism from list-append to ∙ᵀ. This is the
  -- algebra of "posting the journal to the ledger": the running total of
  -- a concatenation is the ∙ᵀ of the totals.
  total-++ : ∀ xs ys → total (xs ++ ys) ≈ᵀ (total xs ∙ᵀ total ys)
  total-++ []       ys = sym (identityˡ (total ys))
  total-++ (p ∷ xs) ys = begin
    proj₂ p ∙ᵀ total (xs ++ ys)        ≈⟨ ∙-congˡ (total-++ xs ys) ⟩
    proj₂ p ∙ᵀ (total xs ∙ᵀ total ys)  ≈⟨ assoc (proj₂ p) (total xs) (total ys) ⟨
    (proj₂ p ∙ᵀ total xs) ∙ᵀ total ys  ∎

  -- Posting one balanced transaction onto another stays balanced:
  -- ledger + journal = ledger. The proof is "zero ∙ᵀ zero is zero".
  post : Tx → Tx → Tx
  post (xs , bx) (ys , by) = (xs ++ ys) , (begin
    total (xs ++ ys)       ≈⟨ total-++ xs ys ⟩
    total xs ∙ᵀ total ys   ≈⟨ ∙-cong bx by ⟩
    εᵀ ∙ᵀ εᵀ               ≈⟨ identityˡ εᵀ ⟩
    εᵀ                     ∎)

  ----------------------------------------------------------------------
  -- The fundamental transaction: move an amount between two accounts by
  -- debiting one and crediting the other.
  --
  -- This debits `a` to debitAcct (posting [ a // 𝟘 ]) and credits `a`
  -- to creditAcct (posting [ 𝟘 // a ]). Those two postings are *inverse*
  -- T-accounts, which is why the transaction balances -- the double-
  -- entry principle "equal debits and credits" is literally x ∙ᵀ x⁻¹ᵀ.

  swapRaw : Amount → Fin n → Fin n → RawTx
  swapRaw a debitAcct creditAcct =
    (debitAcct  , a // 𝟘) ∷
    (creditAcct , 𝟘 // a) ∷
    []

  swapBalanced : ∀ a d c → Balanced (swapRaw a d c)
  swapBalanced a d c = begin
    (a // 𝟘) ∙ᵀ ((𝟘 // a) ∙ᵀ εᵀ)  ≈⟨ ∙-congˡ (identityʳ (𝟘 // a)) ⟩
    (a // 𝟘) ∙ᵀ (𝟘 // a)           ≈⟨ inverseʳ (a // 𝟘) ⟩
    εᵀ                              ∎

  swap : Amount → Fin n → Fin n → Tx
  swap a d c = swapRaw a d c , swapBalanced a d c

------------------------------------------------------------------------
-- A worked example
--
-- Two incommensurate currencies (a 2-vector of [usd , eur]) and three
-- accounts. A $10 cash sale is recorded by debiting Cash and crediting
-- Revenue -- one swap transaction.

module ExampleSystem where

  open Accounting 2 3

  usd eur : Amount
  usd = 1 ∷ 0 ∷ []
  eur = 0 ∷ 1 ∷ []

  cash revenue equity : Fin 3
  cash    = zero
  revenue = suc zero
  equity  = suc (suc zero)

  -- Scalar multiplication of an amount (k copies of a currency).
  infixl 7 _*_
  _*_ : ℕ → Amount → Amount
  k * x = Vec.map (k ℕ.*_) x

  -- Debit Cash, credit Revenue, $10. Balanced by construction.
  cashSale : Tx
  cashSale = swap (10 * usd) cash revenue
