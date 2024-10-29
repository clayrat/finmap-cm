open import Prelude

open import Order.Base
open import Order.Strict
open import Order.Trichotomous
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Meet.Reasoning as Meets

open import Data.List.Correspondences.Unary.Related

import KVList
import KVList.Ord
open import KVMap

module KVMap.Ord
  {ℓᵏ ℓᵛ ℓ ℓ′ : Level}
  {K< : StrictPoset ℓᵏ ℓ}
  ⦃ d : is-trichotomous K< ⦄
  {V≤ : Poset ℓᵛ ℓ′}
  where

  open StrictPoset K< renaming (Ob to K)
  open Poset V≤ renaming (Ob to V)
  open is-trichotomous d hiding (Ob ; _<_ ; <-asym ; <-trans ; <→≠)
  open KVList.Ops {K< = K<} {V = V}
  open KVList.Ord {K< = K<} {V≤ = V≤}
  open KVMap.KVMap
  open KVOps

  kv-poset : Poset (ℓᵏ ⊔ ℓᵛ ⊔ ℓ) (ℓᵏ ⊔ ℓᵛ ⊔ ℓ′)
  kv-poset .Poset.Ob = KVMap.KVMap K< V
  kv-poset .Poset._≤_ x y = x .kv ≤kv y .kv
  kv-poset .Poset.≤-thin {y} = KV≤-prop (y .inv)
  kv-poset .Poset.≤-refl = KV≤-refl
  kv-poset .Poset.≤-trans = KV≤-trans
  kv-poset .Poset.≤-antisym {y = kvmap _ iy} xy yx =
    ap² kvmap (KV≤-antisym xy yx) (to-pathᴾ (hlevel 1 _ iy))

  kv-bot : Bottom kv-poset
  kv-bot .Bottom.bot = emptym K< V
  kv-bot .Bottom.has-bot x = KV≤-init

  module KVJoins {Vj : Has-joins V≤} where

    open Joins V≤ Vj

    kv-joins : Has-joins kv-poset
    kv-joins {x} {y} .Join.lub      = unionm K< V _∪_ x y
    kv-joins {x} {y} .Join.has-join =
      let lr = union-≤-lr {f = _∪_} {xs = x .kv} {ys = y .kv} λ a b → l≤∪ , r≤∪ in
      record {
        l≤join = lr .fst
      ; r≤join = lr .snd
      ; least = λ ub lx ly → union-≤-least (x .kv) (y .kv) (ub .kv) (ub .inv) (λ a b → ∪-universal) lx ly
      }

  module KVMeets {Vm : Has-meets V≤} where

    open Meets V≤ Vm

    kv-meets : Has-meets kv-poset
    kv-meets {x} {y} .Meet.glb      = interm K< V _∩_ x y
    kv-meets {x} {y} .Meet.has-meet =
      let lr = inter-≤-lr {f = _∩_} {xs = x .kv} {ys = y .kv} λ a b → ∩≤l , ∩≤r in
      record {
        meet≤l = lr .fst
      ; meet≤r = lr .snd
      ; greatest = λ lb lx ly → inter-≤-greatest (x .inv) (y .inv) (λ a b → ∩-universal) lx ly
      }
