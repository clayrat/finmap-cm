module KVMap where

open import Prelude

open import Order.Strict
open import Order.Trichotomous
open import Data.Maybe
open import Data.List
open import Data.List.Correspondences.Unary.Related

import KVList

private variable
  ℓᵏ ℓᵛ ℓ : Level

record KVMap
  (K< : StrictPoset ℓᵏ ℓ)
  (V : 𝒰 ℓᵛ) : 𝒰 (ℓ ⊔ ℓᵏ ⊔ ℓᵛ) where

  constructor kvmap
  field
    kv  : List (⌞ K< ⌟ × V)
    inv : KVList.Is-kvlist {K< = K<} kv

open KVMap

unquoteDecl KVMap-iso = declare-record-iso KVMap-iso (quote KVMap)

module KVOps
  (K< : StrictPoset ℓᵏ ℓ)
  ⦃ d : is-trichotomous K< ⦄
  (V : 𝒰 ℓᵛ)
  where

  open StrictPoset K< renaming (Ob to K)
  open KVList
  open KVList.Ops

  emptym : KVMap K< V
  emptym .kv  = empty-kv {K< = K<}
  emptym .inv = Is-kvlist-empty {V = V}

  lookupm : K → KVMap K< V → Maybe V
  lookupm k m = lookup-kv k (m .kv)

  upsertm : (V → V → V) → K → V → KVMap K< V → KVMap K< V
  upsertm f k v m .kv  = upsert-kv f k v (m .kv)
  upsertm f k v m .inv = Is-kvlist-upsert (m .inv)

  removem : K → KVMap K< V → KVMap K< V
  removem k m .kv  = remove-kv k (m .kv)
  removem k m .inv = Is-kvlist-remove (m .inv)

  unionm : (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
  unionm f l r .kv  = union-kv f (l .kv) (r .kv)
  unionm f l r .inv = Is-kvlist-union (l .inv) (r .inv)

  interm : (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
  interm f l r .kv  = inter-kv f (l .kv) (r .kv)
  interm f l r .inv = Is-kvlist-inter (l .inv) (r .inv)

  -- properties

  kv-ext : {kv₁ kv₂ : KVMap K< V} → kv₁ .kv ＝ kv₂ .kv → kv₁ ＝ kv₂
  kv-ext {kv₂ = kvmap _ inv₂} e = ap² kvmap e (to-pathᴾ (hlevel 1 _ inv₂))
