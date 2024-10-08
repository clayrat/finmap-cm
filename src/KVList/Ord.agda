open import Prelude

open import Order.Base
open import Order.Strict
open import Order.Trichotomous

open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat.Order.Base renaming (_<_ to _<ⁿ_ ; _≤_ to _≤ⁿ_ ; <-trans to <ⁿ-trans ; <-asym to <ⁿ-asym ; <→≠ to <ⁿ→≠)
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

open import KVList

module KVList.Ord
  {ℓᵏ ℓᵛ ℓ ℓ′ : Level}
  {K< : StrictPoset ℓᵏ ℓ}
  {V≤ : Poset ℓᵛ ℓ′}
  ⦃ d : is-trichotomous K< ⦄

  where

  open StrictPoset K< renaming (Ob to K)
  open Poset V≤ renaming (Ob to V)
  open is-trichotomous d hiding (Ob ; _<_ ; <-asym ; <-trans ; <→≠)

--  open KVList {K< = K<} {V}

  data _≤kv_ : List (K × V) → List (K × V) → 𝒰 (ℓᵏ ⊔ ℓᵛ ⊔ ℓ′) where
    kvdone : [] ≤kv []
    kvtake : ∀ {kx ky vx vy xs ys}
           → kx ＝ ky → vx ≤ vy → xs ≤kv ys
           → ((kx , vx) ∷ xs) ≤kv ((ky , vy) ∷ ys)
    kvdrop : ∀ {xs ky vy ys}
           → xs ≤kv ys
           → xs ≤kv ((ky , vy) ∷ ys)

  KV≤-all : {xs ys : List (K × V)}
          → Is-kvlist ys
          → xs ≤kv ys
          → All (λ where (kx , vx) →
                           Σ[ vy ꞉ V ] (lookup-kv kx ys ＝ just vy) × (vx ≤ vy))
                xs
  KV≤-all {xs = .[]}            {ys = .[]}             _       kvdone                                         = []
  KV≤-all {xs = (kx , vx) ∷ xs} {ys = (ky , vy) ∷ ys} (∷ˢ ry) (kvtake {kx} {ky} {vx} {vy} {xs} {ys} ex lx le) =
    ( vy
    , given-eq ex
        return (λ q → recᵗ nothing (just vy) (lookup-kv kx ys) q ＝ just vy)
        then refl
    , lx)
    ∷ all-map
        (λ {x} → λ where
             (vy′ , ey′ , le′) →
                 vy′
               , given-gt All→∀Has (related→all ry) (x .fst) (lookup-has ey′)
                   return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy′)
                   then ey′
               , le′)
        (KV≤-all (related→sorted ry) le)
  KV≤-all {xs = xs}             {ys = (ky , vy) ∷ ys} (∷ˢ ry) (kvdrop {xs} {ky} {vy} {ys} le)                 =
    all-map
      (λ {x} → λ where
             (vy′ , ey′ , le′) →
                  vy′
                , given-gt All→∀Has (related→all ry) (x .fst) (lookup-has ey′)
                   return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy′)
                   then ey′
                , le′)
      (KV≤-all (related→sorted ry) le)

  KV≤-l : {xs : List (K × V)} → [] ≤kv xs
  KV≤-l {xs = []}           = kvdone
  KV≤-l {xs = (k , v) ∷ xs} = kvdrop KV≤-l

  KV≤-refl : {xs : List (K × V)} → xs ≤kv xs
  KV≤-refl {xs = []}           = kvdone
  KV≤-refl {xs = (k , v) ∷ xs} = kvtake refl refl KV≤-refl

  KV≤-trans : {xs ys zs : List (K × V)} → xs ≤kv ys → ys ≤kv zs → xs ≤kv zs
  KV≤-trans                          {ys = .[]}               {zs = .[]}                xy                                 kvdone                                                                         = xy
  KV≤-trans {xs = .((kx , vx) ∷ xs)} {ys = .((ky , vy) ∷ ys)} {zs = .((kz , vz) ∷ zs)} (kvtake {kx} {vx} {xs} exy lxy xy) (kvtake {kx = ky} {ky = kz} {vx = vy} {vy = vz} {xs = ys} {ys = zs} eyz lyz yz) =
    kvtake (exy ∙ eyz) (lxy ∙ lyz) (KV≤-trans xy yz)
  KV≤-trans                          {ys = .((ky , vy) ∷ ys)} {zs = .((kz , vz) ∷ zs)} (kvdrop xy)                        (kvtake {kx = ky} {ky = kz} {vx = vy} {vy = vz} {xs = ys} {ys = zs} ez lz yz)   =
    kvdrop (KV≤-trans xy yz)
  KV≤-trans                                                   {zs = .((kz , vz) ∷ zs)}  xy                                (kvdrop {ky = kz} {vy = vz} {ys = zs} yz)                                       =
    kvdrop (KV≤-trans xy yz)

  -- remove

  remove-≤ : {k : K} {xs : List (K × V)} → remove-kv k xs ≤kv xs
  remove-≤     {xs = []}             = kvdone
  remove-≤ {k} {xs = (kx , vx) ∷ xs} with trisect k kx
  ... | LT k<kx = KV≤-refl
  ... | EQ k=kx = kvdrop KV≤-refl
  ... | GT kx<k = kvtake refl refl remove-≤

  -- union

  union-≤-lr-aux : {f : V → V → V} (xs ys : List (K × V))
                 → (∀ x y → (x ≤ f x y) × (y ≤ f x y))
                 → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                 → (xs ≤kv union-kv f xs ys) × (ys ≤kv union-kv f xs ys)
  union-≤-lr-aux      []               _               _    _        = KV≤-l , KV≤-refl
  union-≤-lr-aux     ((kx , vx) ∷ xs)  []              _    _        = KV≤-refl , KV≤-l
  union-≤-lr-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) fle (acc rec) with trisect kx ky
  ... | LT x<y =
    let (ihl , ihr) = union-≤-lr-aux {f = f} xs ((ky , vy) ∷ ys)
                                     fle
                                     (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
      in
    kvtake refl refl ihl , kvdrop ihr
  ... | EQ x=y =
    let (ihl , ihr) = union-≤-lr-aux {f = f} xs ys
                                     fle
                                     (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                                             (  ap suc (++-length xs ys)
                                                              ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                              ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                             <-ascend)))
        (fl , fr) = fle vx vy
      in
    kvtake refl fl ihl , kvtake (x=y ⁻¹) fr ihr
  ... | GT y<x =
    let (ihl , ihr) = union-≤-lr-aux {f = f} ((kx , vx) ∷ xs) ys
                                     fle
                                     (rec (((kx , vx) ∷ xs) ++ ys)
                                          (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                      (  ap suc (++-length xs ys)
                                                       ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                       ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                      <-ascend)))
      in
    kvdrop ihl , kvtake refl refl ihr

  union-≤-lr : {f : V → V → V} {xs ys : List (K × V)}
             → (∀ x y → (x ≤ f x y) × (y ≤ f x y))
             → (xs ≤kv union-kv f xs ys) × (ys ≤kv union-kv f xs ys)
  union-≤-lr {f} {xs} {ys} fle = union-≤-lr-aux {f = f} xs ys fle (Acc-on length (xs ++ ys) (<-wf (length (xs ++ ys))))

  -- inter

  inter-≤-lr-aux : {f : V → V → V} (xs ys : List (K × V))
                 → (∀ x y → (f x y ≤ x) × (f x y ≤ y))
                 → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                 → (inter-kv f xs ys ≤kv xs) × (inter-kv f xs ys ≤kv ys)
  inter-≤-lr-aux     []                ys              fle ac        = kvdone , KV≤-l
  inter-≤-lr-aux     (_ ∷ _)           []              fle ac        = KV≤-l , kvdone
  inter-≤-lr-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) fle (acc rec) with trisect kx ky
  ... | LT x<y =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} xs ((ky , vy) ∷ ys)
                                     fle
                                     (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
      in
    kvdrop ihl , ihr
  ... | EQ x=y =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} xs ys
                                     fle
                                     (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                                             (  ap suc (++-length xs ys)
                                                              ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                              ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                             <-ascend)))
        (fl , fr) = fle vx vy
      in
    kvtake refl fl ihl , kvtake x=y fr ihr
  ... | GT y<x =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} ((kx , vx) ∷ xs) ys
                                     fle
                                     (rec (((kx , vx) ∷ xs) ++ ys)
                                          (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                      (  ap suc (++-length xs ys)
                                                       ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                       ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                      <-ascend)))
      in
    ihl , kvdrop ihr

  inter-≤-lr : {f : V → V → V} {xs ys : List (K × V)}
             → (∀ x y → (f x y ≤ x) × (f x y ≤ y))
             → (inter-kv f xs ys ≤kv xs) × (inter-kv f xs ys ≤kv ys)
  inter-≤-lr {f} {xs} {ys} fle = inter-≤-lr-aux {f = f} xs ys fle (Acc-on length (xs ++ ys) (<-wf (length (xs ++ ys))))

