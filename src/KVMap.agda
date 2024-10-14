module KVMap where

open import Prelude

open import Order.Strict
open import Order.Trichotomous

open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat.Order.Base renaming (_<_ to _<ⁿ_ ; <-trans to <ⁿ-trans ; <-asym to <ⁿ-asym ; <→≠ to <ⁿ→≠)
open import Data.Bool renaming (elim to elimᵇ ; rec to recᵇ)
open import Data.Maybe renaming (elim to elimᵐ ; rec to recᵐ)
open import Data.Dec
open import Data.Reflects
open import Data.Dec.Tri renaming (elim to elimᵗ ; rec to recᵗ)
open import Data.Wellfounded

open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Has
open import Data.List.Correspondences.Unary.At
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Binary.Perm
open import Data.List.Correspondences.Binary.OPE

import KVList

private variable
  ℓᵏ ℓᵛ ℓ : Level
  K< : StrictPoset ℓᵏ ℓ
  V : 𝒰 ℓᵛ
  
record KVMap
  (K< : StrictPoset ℓᵏ ℓ) 
  ⦃ d : is-trichotomous K< ⦄
  (V : 𝒰 ℓᵛ) : 𝒰 (ℓ ⊔ ℓᵏ ⊔ ℓᵛ) where

  constructor kvmap

  open StrictPoset K< renaming (Ob to K)
  open KVList {K< = K<} {V = V}

  field
    kv  : List (K × V)
    inv : Is-kvlist kv

open KVMap

emptym : ⦃ d : is-trichotomous K< ⦄
       → KVMap K< V
emptym     .kv = KVList.empty-kv
emptym {V} .inv = KVList.Is-kvlist-empty {V = V}

lookupm : ⦃ d : is-trichotomous K< ⦄
        → ⌞ K< ⌟ → KVMap K< V → Maybe V
lookupm k m = KVList.lookup-kv k (m .kv)        

upsertm : ⦃ d : is-trichotomous K< ⦄
        → (V → V → V) → ⌞ K< ⌟ → V → KVMap K< V → KVMap K< V
upsertm f k v m .kv  = KVList.upsert-kv f k v (m .kv)
upsertm f k v m .inv = KVList.Is-kvlist-upsert (m .inv)

removem : ⦃ d : is-trichotomous K< ⦄
        → ⌞ K< ⌟ → KVMap K< V → KVMap K< V
removem k m .kv  = KVList.remove-kv k (m .kv)
removem k m .inv = KVList.Is-kvlist-remove (m .inv)

unionm : ⦃ d : is-trichotomous K< ⦄
       → (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
unionm f l r .kv  = KVList.union-kv f (l .kv) (r .kv)
unionm f l r .inv = KVList.Is-kvlist-union (l .inv) (r .inv)

interm : ⦃ d : is-trichotomous K< ⦄
       → (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
interm f l r .kv  = KVList.inter-kv f (l .kv) (r .kv)
interm f l r .inv = KVList.Is-kvlist-inter (l .inv) (r .inv)
