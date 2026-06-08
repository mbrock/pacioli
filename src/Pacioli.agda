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
open import Algebra.Bundles using (CommutativeMonoid; AbelianGroup; Group)
open import Algebra.Structures using (IsAbelianGroup)
import Algebra.Definitions as Def
import Algebra.Construct.Pointwise as Pointwise
import Algebra.Construct.Sub.Group
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
open import Data.Vec.Functional as V using (Vector; replicate)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_; proj₁; Σ-syntax)

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
  PacioliGroup = record
    { Carrier = DebitCredit Carrier
    ; _≈_ = _≈ᵀ_
    ; _∙_ = _∙ᵀ_
    ; ε = εᵀ
    ; _⁻¹ = _⁻¹ᵀ
    ; isAbelianGroup = isPacioliGroup
    }

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
              { isEquivalence = record
                { refl = ≡-refl
                ; sym = ≡-sym
                ; trans = ≡-trans
                }
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = Vecₚ.zipWith-assoc ℕ.+-assoc
            }
          ; identity =
              Vecₚ.zipWith-identityˡ ℕ.+-identityˡ
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

------------------------------------------------------------------------
-- Accounting: rows, the trial balance, and balanced transactions
--
-- The bookkeeping vocabulary lines up with the algebra:
--   * a row / journal entry / ledger = one T-account per named account,
--     i.e. an element of the n-fold product of the Pacioli group
--   * the trial balance              = the group sum of a row (stdlib's
--                                      finite summation over a monoid)
--   * a balanced row / transaction   = a row whose trial balance is εᵀ
--
-- The balanced rows are exactly the kernel of the trial balance, and the
-- kernel of a group homomorphism is a subgroup. So "the initial ledger
-- balances" and "posting a balanced row keeps it balanced" are not
-- invariants we maintain -- they are closure of that subgroup, free.

module Accounting (m n : ℕ) where

  open NonNegativeVectors m using (Amounts; +-cancelˡ)
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

  -- Finite summation over the Pacioli group -- the trial balance -- and
  -- its distributivity over account-wise addition, both straight from
  -- the standard library's summation-over-a-(commutative-)monoid.
  open import Algebra.Properties.CommutativeMonoid.Sum commutativeMonoid
    using (sum; ∑-distrib-+)
  open import Algebra.Properties.AbelianGroup P.PacioliGroup
    using (⁻¹-∙-comm; ε⁻¹≈ε)

  -- A row assigns a T-account to each of the n named accounts. The rows
  -- are the n-fold product of the Pacioli group -- an abelian group under
  -- account-wise operations -- which the stdlib hands us for free as the
  -- pointwise lifting of the Pacioli group over the index set Fin n.
  RowGroup : AbelianGroup 0ℓ 0ℓ
  RowGroup = Pointwise.abelianGroup (Fin n) P.PacioliGroup

  open AbelianGroup RowGroup using () renaming
    ( Carrier to Row ; _≈_ to _≈ᴿ_ ; _∙_ to _∙ᴿ_
    ; ε to εᴿ ; _⁻¹ to _⁻¹ᴿ ; refl to reflᴿ )

  -- The trial balance of a row: sum its T-accounts in the Pacioli group.
  total : Row → T
  total f = sum f

  -- A row balances when its trial balance is the zero-account -- the
  -- double-entry principle. The balanced rows are exactly ker total.
  Balanced : Row → Set
  Balanced f = total f ≈ᵀ εᵀ

  Tx : Set
  Tx = Σ[ f ∈ Row ] Balanced f

  ----------------------------------------------------------------------
  -- ker total is a subgroup: it contains the zero row and is closed
  -- under account-wise addition. So the initial ledger balances and
  -- posting stays balanced -- closure, not per-post bookkeeping.

  -- The trial balance of the all-zero row is εᵀ (a sum of zeroes). The
  -- size is explicit because `replicate` discards it, so leaving it
  -- implicit would strand `sum`'s size as an unsolved metavariable.
  total-ε : ∀ k → sum {k} (replicate k εᵀ) ≈ᵀ εᵀ
  total-ε ℕ.zero    = refl
  total-ε (ℕ.suc k) = trans (identityˡ _) (total-ε k)

  -- The empty / initial ledger: every account at the zero-account.
  empty : Tx
  empty = εᴿ , total-ε n

  -- Posting two balanced rows: add account-wise. Balance is preserved by
  -- ∑-distrib-+ (total is a homomorphism) -- "zero ∙ᵀ zero is zero".
  post : Tx → Tx → Tx
  post (f , bf) (g , bg) = (f ∙ᴿ g) , (begin
    total (f ∙ᴿ g)      ≈⟨ ∑-distrib-+ f g ⟩
    total f ∙ᵀ total g  ≈⟨ ∙-cong bf bg ⟩
    εᵀ ∙ᵀ εᵀ            ≈⟨ identityˡ εᵀ ⟩
    εᵀ                  ∎)

  ----------------------------------------------------------------------
  -- A single posting: the row that is the T-account `v` at account `i`
  -- and the zero-account everywhere else. Its trial balance is just `v`.

  δ : ∀ {k} → Fin k → T → Vector T k
  δ zero    v = v V.∷ replicate _ εᵀ
  δ (suc i) v = εᵀ V.∷ δ i v

  total-δ : ∀ {k} (i : Fin k) v → sum (δ i v) ≈ᵀ v
  total-δ {ℕ.suc k} zero    v = trans (∙-congˡ (total-ε k)) (identityʳ v)
  total-δ           (suc i) v = trans (identityˡ _) (total-δ i v)

  ----------------------------------------------------------------------
  -- The fundamental transaction: move an amount between two accounts by
  -- debiting one and crediting the other. The debit posting [ a // 𝟘 ]
  -- and the credit posting [ 𝟘 // a ] are *inverse* T-accounts, so the
  -- row balances: the double-entry principle is literally x ∙ᵀ x⁻¹ᵀ.

  swapRow : Amount → Fin n → Fin n → Row
  swapRow a debitAcct creditAcct =
    δ debitAcct (a // 𝟘) ∙ᴿ δ creditAcct (𝟘 // a)

  swapBalanced : ∀ a d c → Balanced (swapRow a d c)
  swapBalanced a d c = begin
    total (δ d (a // 𝟘) ∙ᴿ δ c (𝟘 // a))         ≈⟨ ∑-distrib-+ (δ d (a // 𝟘)) (δ c (𝟘 // a)) ⟩
    total (δ d (a // 𝟘)) ∙ᵀ total (δ c (𝟘 // a))  ≈⟨ ∙-cong (total-δ d (a // 𝟘)) (total-δ c (𝟘 // a)) ⟩
    (a // 𝟘) ∙ᵀ (𝟘 // a)                          ≈⟨ inverseʳ (a // 𝟘) ⟩
    εᵀ                                             ∎

  swap : Amount → Fin n → Fin n → Tx
  swap a d c = swapRow a d c , swapBalanced a d c

  ----------------------------------------------------------------------
  -- Reversing a transaction: negate every account. This needs that the
  -- trial balance commutes with inversion -- total is a *group* homo,
  -- not merely a monoid one -- which is what upgrades ker total from
  -- "closed under ∙ᴿ" to a genuine subgroup.

  total-⁻¹ : ∀ {k} (f : Vector T k) → sum (λ i → f i ⁻¹ᵀ) ≈ᵀ (sum f) ⁻¹ᵀ
  total-⁻¹ {ℕ.zero}  f = sym ε⁻¹≈ε
  total-⁻¹ {ℕ.suc k} f =
    trans (∙-congˡ (total-⁻¹ (V.tail f)))
          (⁻¹-∙-comm (V.head f) (sum (V.tail f)))

  reverse : Tx → Tx
  reverse (f , bf) = (f ⁻¹ᴿ) , (begin
    total (f ⁻¹ᴿ)  ≈⟨ total-⁻¹ f ⟩
    (total f) ⁻¹ᵀ  ≈⟨ ⁻¹-cong bf ⟩
    εᵀ ⁻¹ᵀ         ≈⟨ ε⁻¹≈ε ⟩
    εᵀ             ∎)

  ----------------------------------------------------------------------
  -- Balanced transactions as a subgroup.
  --
  -- empty / post / reverse are the identity, multiplication and inverse
  -- of the balanced rows under account-wise operations. Presenting them
  -- through the stdlib's Subgroup -- the kernel of the trial balance
  -- total : RowGroup ⟶ PacioliGroup, given as the injection
  -- proj₁ : Tx ↪ Row -- pulls back all the group laws. Because the
  -- subgroup's equality *is* equality of the underlying rows, the
  -- monomorphism witness is pure refl / identity: the closure proofs
  -- (empty, post, reverse) are the only real content, exactly as it
  -- should be.

  module Sub = Algebra.Construct.Sub.Group (AbelianGroup.group RowGroup)

  balancedSubgroup : Sub.Subgroup 0ℓ 0ℓ
  balancedSubgroup = record
    { domain = record
        { Carrier = Tx
        ; _≈_     = λ x y → proj₁ x ≈ᴿ proj₁ y
        ; _∙_     = post
        ; ε       = empty
        ; _⁻¹     = reverse
        }
    ; ι = proj₁
    ; ι-monomorphism = record
        { isGroupHomomorphism = record
            { isMonoidHomomorphism = record
                { isMagmaHomomorphism = record
                    { isRelHomomorphism = record { cong = λ p → p }
                    ; homo = λ _ _ → reflᴿ
                    }
                ; ε-homo = reflᴿ
                }
            ; ⁻¹-homo = λ _ → reflᴿ
            }
        ; injective = λ p → p
        }
    }

  -- ...and so the balanced transactions are a group in their own right.
  TxGroup : Group 0ℓ 0ℓ
  TxGroup = Sub.Subgroup.group balancedSubgroup

------------------------------------------------------------------------
-- SPSC ring buffers as bounded T-accounts
--
-- The specification is deliberately just two monotone counters and two
-- bounds. The Pacioli account below is the accounting model of those
-- counters, not the admission controller: enqueue/dequeue constructors
-- require the non-negativity guards, and the verified layer packages
-- the usual empty-plus-preservation closure proof.

module RingBuffer (N : ℕ) where

  record State : Set where
    constructor ring
    field
      head : ℕ
      tail : ℕ

  open State public

  -- Freestanding specification: occupancy is head - tail and free space
  -- is (tail + N) - head. Safety is exactly the two halfspace guards.
  Occupancy : State → ℕ
  Occupancy s = head s ℕ.∸ tail s

  Free : State → ℕ
  Free s = (tail s ℕ.+ N) ℕ.∸ head s

  NoUnderflow : State → Set
  NoUnderflow s = tail s ℕ.≤ head s

  NoOverflow : State → Set
  NoOverflow s = head s ℕ.≤ tail s ℕ.+ N

  HasRoom : State → Set
  HasRoom s = head s ℕ.< tail s ℕ.+ N

  HasItem : State → Set
  HasItem s = tail s ℕ.< head s

  record Safe (s : State) : Set where
    constructor safe
    field
      noUnderflow : NoUnderflow s
      noOverflow  : NoOverflow s

  open Safe public

  emptyState : State
  emptyState = ring 0 0

  enqueue : (s : State) → HasRoom s → State
  enqueue s _ = ring (ℕ.suc (head s)) (tail s)

  dequeue : (s : State) → HasItem s → State
  dequeue s _ = ring (head s) (ℕ.suc (tail s))

  emptySafe : Safe emptyState
  emptySafe = safe ℕ.z≤n ℕ.z≤n

  enqueueSafe : ∀ s → Safe s → (room : HasRoom s) → Safe (enqueue s room)
  enqueueSafe s ok room = safe
    (ℕ.m≤n⇒m≤1+n (noUnderflow ok))
    room

  dequeueSafe : ∀ s → Safe s → (item : HasItem s) → Safe (dequeue s item)
  dequeueSafe s ok item = safe
    item
    (ℕ.m≤n⇒m≤1+n (noOverflow ok))

  ----------------------------------------------------------------------
  -- Accounting model.
  --
  -- Over ℕ, the Pacioli group is the group of differences of the two
  -- counters: [ head // tail ]. Posting one enqueue debits the head
  -- counter; posting one dequeue credits the tail counter.

  module P = Pacioli ℕ.+-0-commutativeMonoid ℕ.+-cancelˡ-≡
  open AbelianGroup P.PacioliGroup
    renaming (Carrier to T; _≈_ to _≈ᵀ_; _∙_ to _∙ᵀ_; ε to εᵀ; _⁻¹ to _⁻¹ᵀ)

  account : State → T
  account s = head s // tail s

  enqueuePosting : T
  enqueuePosting = 1 // 0

  dequeuePosting : T
  dequeuePosting = 0 // 1

  ----------------------------------------------------------------------
  -- Verified layer: the same guard propositions drive the typed API.

  record Verified : Set where
    constructor verified
    field
      state : State
      proof : Safe state

  open Verified public

  empty : Verified
  empty = verified emptyState emptySafe

  enqueueᵛ : (b : Verified) → HasRoom (state b) → Verified
  enqueueᵛ b room = verified (enqueue (state b) room)
                             (enqueueSafe (state b) (proof b) room)

  dequeueᵛ : (b : Verified) → HasItem (state b) → Verified
  dequeueᵛ b item = verified (dequeue (state b) item)
                             (dequeueSafe (state b) (proof b) item)

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
