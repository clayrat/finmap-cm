open import Prelude

open import Order.Strict
open import Order.Trichotomous

open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat.Order.Base renaming (_<_ to _<ⁿ_ ; <-trans to <ⁿ-trans ; <→≠ to <ⁿ→≠)
open import Data.Bool renaming (elim to elimᵇ ; rec to recᵇ)
open import Data.Maybe renaming (elim to elimᵐ ; rec to recᵐ)
open import Data.Dec
open import Data.Reflects
open import Data.Tri renaming (elim to elimᵗ ; rec to recᵗ)
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

module KVList 
  {ℓᵏ ℓᵛ ℓ : Level}
  {K< : StrictPoset ℓᵏ ℓ}
  {V : 𝒰 ℓᵛ}
  ⦃ d : is-trichotomous K< ⦄
  where

  open StrictPoset K< public renaming (Ob to K)

  empty-kv : List (K × V)
  empty-kv = []

  lookup-kv : K → List (K × V) → Maybe V
  lookup-kv k []             = nothing
  lookup-kv k ((k₀ , v₀) ∷ xs) =
    caseᵗ k >=< k₀
      lt⇒ nothing
      eq⇒ just v₀
      gt⇒ lookup-kv k xs
      
  upsert-kv : (V → V → V) → K → V → List (K × V) → List (K × V)
  upsert-kv f k v      []            = (k , v) ∷ []
  upsert-kv f k v xs₀@((x , w) ∷ xs) =
    caseᵗ k >=< x
      lt⇒ (k , v) ∷ xs₀
      eq⇒ (k , f w v) ∷ xs
      gt⇒ ((x , w) ∷ upsert-kv f k v xs)

  remove-kv : K → List (K × V) → List (K × V)
  remove-kv k      []            = []
  remove-kv k xs₀@((x , v) ∷ xs) =
    caseᵗ k >=< x
      lt⇒ xs₀
      eq⇒ xs 
      gt⇒ ((x , v) ∷ remove-kv k xs)

  union-kv : (V → V → V) → List (K × V) → List (K × V) → List (K × V)
  union-kv f      []                   ys              = ys
  union-kv f xs₀@(_ ∷ _)               []              = xs₀
  union-kv f xs₀@((kx , vx) ∷ xs) ys₀@((ky , vy) ∷ ys) =
    caseᵗ kx >=< ky
      lt⇒ ((kx , vx) ∷ union-kv f xs ys₀) 
      eq⇒ ((kx , f vx vy) ∷ union-kv f xs ys) 
      gt⇒ ((ky , vy) ∷ union-kv f xs₀ ys) 

  inter-kv : (V → V → V) → List (K × V) → List (K × V) → List (K × V)
  inter-kv f      []                   _               = []
  inter-kv f     (_ ∷ _)               []              = []
  inter-kv f xs₀@((kx , vx) ∷ xs) ys₀@((ky , vy) ∷ ys) =
    caseᵗ kx >=< ky
      lt⇒ (inter-kv f xs ys₀) 
      eq⇒ ((kx , f vx vy) ∷ inter-kv f xs ys) 
      gt⇒ (inter-kv f xs₀ ys) 

  keys : List (K × V) → List K
  keys = map fst

  values : List (K × V) → List V
  values = map snd

  -- properties

  Is-kvlist : List (K × V) → 𝒰 (ℓ ⊔ ℓᵏ)
  Is-kvlist xs = Sorted _<_ (keys xs)

  keys-++ : ∀ {xs ys} → keys (xs ++ ys) ＝ keys xs ++ keys ys
  keys-++ {xs} {ys} = map-++ fst xs ys

  -- lookup

  lookup-related : ∀ {k xs}
                 → Related _<_ k (keys xs) → lookup-kv k xs ＝ nothing {- is-nothing? -}
  lookup-related     {xs = []}              r          = refl
  lookup-related {k} {xs = (k₀ , v₀) ∷ xs} (k<k₀ ∷ʳ _) =
    given-lt k<k₀
       return (λ q → recᵗ nothing (just v₀) (lookup-kv k xs) q ＝ nothing)
       then refl

  lookup-not-has : ∀ {k xs}
                 → ¬ Has k (keys xs) → lookup-kv k xs ＝ nothing {- is-nothing? -}
  lookup-not-has     {xs = []}             _  = refl
  lookup-not-has {k} {xs = (k₀ , v₀) ∷ xs} nh with d .is-trichotomous.trisect k k₀
  ... | lt _ _    _ = refl
  ... | eq _ k=k₀ _ = absurd (nh (here (k=k₀ ⁻¹)))
  ... | gt _ _    _ = lookup-not-has (nh ∘ there)

  -- empty

  Is-kvlist-empty : Is-kvlist empty-kv
  Is-kvlist-empty = []ˢ

  lookup-empty : ∀ {k} → lookup-kv k empty-kv ＝ nothing
  lookup-empty = refl

  -- upsert

  kvlist-upsert-perm : {f : V → V → V} {k : K} {v : V} {xs : List (K × V)}
                     → Is-kvlist xs
                     → Perm (keys (upsert-kv f k v xs))
                            (if has ⦃ d = Tri→discrete ⦄ k (keys xs)
                               then keys xs
                               else k ∷ keys xs)
  kvlist-upsert-perm             {xs = []}              ikv   = perm-refl
  kvlist-upsert-perm {f} {k} {v} {xs = (k′ , v′) ∷ xs} (∷ˢ r) with d .is-trichotomous.trisect k k′
  ... | lt k<k′ _    k′≮k =
    given-gt k<k′
      return (λ q → Perm (k ∷ k′ ∷ keys xs)
                         (if ⌊ ⌊ q ⌋≟ ⌋ or has ⦃ d = Tri→discrete ⦄ k (keys xs)
                            then k′ ∷ keys xs
                            else k ∷ k′ ∷ keys xs))
      then
        elimᵇ {P = λ q → has ⦃ d = Tri→discrete ⦄ k (keys xs) ＝ q
                       → Perm (k ∷ k′ ∷ keys xs) 
                              (if q then k′ ∷ keys xs else k ∷ k′ ∷ keys xs)}
              (λ ∈?k → let ∈k = so→true! ⦃ Reflects-has ⦃ d = Tri→discrete ⦄ {xs = keys xs} ⦄ $ so≃is-true ⁻¹ $ ∈?k in
                        absurd (k′≮k $ All→∀Has (related→all r) k ∈k))
              (λ _ → perm-refl)
              (has ⦃ d = Tri→discrete ⦄ k (keys xs))
              refl
  ... | eq _    k=k′ _    =
    given-eq k=k′ ⁻¹
      return (λ q → Perm (k ∷ keys xs)
                         (if ⌊ ⌊ q ⌋≟ ⌋ or has ⦃ d = Tri→discrete ⦄ k (keys xs)
                            then k′ ∷ keys xs
                            else k ∷ k′ ∷ keys xs))
      then pprep k=k′ perm-refl
  ... | gt _    _    k′<k =
    given-lt k′<k
      return (λ q → Perm (k′ ∷ keys (upsert-kv f k v xs))
                         (if ⌊ ⌊ q ⌋≟ ⌋ or has ⦃ d = Tri→discrete ⦄ k (keys xs)
                            then k′ ∷ keys xs
                            else k ∷ k′ ∷ keys xs))
      then
        elimᵇ {P = λ q → Perm (keys (upsert-kv f k v xs))
                             (if q then keys xs else k ∷ keys xs)
                      → Perm (k′ ∷ keys (upsert-kv f k v xs))
                             (if q then k′ ∷ keys xs else k ∷ k′ ∷ keys xs)}
              (pprep refl)
              (λ p → ptrans (pprep refl p) (perm-cons-cat-commassoc {xs = k ∷ []}))
              (has ⦃ d = Tri→discrete ⦄ k (keys xs))
              (kvlist-upsert-perm {xs = xs} (related→sorted r))

  Is-kvlist-upsert : {f : V → V → V} {k : K} {v : V} {xs : List (K × V)}
                   → Is-kvlist xs
                   → Is-kvlist (upsert-kv f k v xs)
  Is-kvlist-upsert             {xs = []}              []ˢ   = ∷ˢ []ʳ
  Is-kvlist-upsert {f} {k} {v} {xs = (k′ , v′) ∷ xs} (∷ˢ r) with d .is-trichotomous.trisect k k′
  ... | lt k<k′ _    _    = ∷ˢ (k<k′ ∷ʳ r)
  ... | eq _    k=k′ _    = ∷ˢ (subst (λ q → Related _<_ q (keys xs)) (k=k′ ⁻¹) r)
  ... | gt _    _    k′<k =
    ∷ˢ (sorted-at0→related
         (Is-kvlist-upsert {f = f} {k = k} {v = v}  {xs = xs} (related→sorted r))
         (all→atweak
            (perm-all (perm-sym (kvlist-upsert-perm (related→sorted r))) $
             let ra = related→all r in
             elimᵇ {P = λ q → All (k′ <_) (if q then keys xs else k ∷ keys xs)}
                   ra (k′<k ∷ ra)
                   (has ⦃ d = Tri→discrete ⦄ k (keys xs)))
            0))

  kvlist-upsert-lookup : {f : V → V → V} {k : K} {v : V} {xs : List (K × V)}
                       → ∀ k′ → lookup-kv k′ (upsert-kv f k v xs) ＝ (if ⌊ _≟_ ⦃ Tri→discrete ⦄ k′ k ⌋
                                                                              then recᵐ (just v) (just ∘ flip f v) (lookup-kv k′ xs)
                                                                              else lookup-kv k′ xs)
  kvlist-upsert-lookup     {k}     {xs = []}             k′ with d .is-trichotomous.trisect k′ k
  ... | lt _ _ _ = refl
  ... | eq _ _ _ = refl
  ... | gt _ _ _ = refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ with d .is-trichotomous.trisect k k₀
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | lt k<k₀ _    _    with d .is-trichotomous.trisect k′ k
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | lt k<k₀ _    _    | lt k′<k  _     _    =
    given-lt (<-trans k′<k k<k₀)
      return (λ q → nothing ＝ recᵗ nothing (just v₀) (lookup-kv k′ xs) q)
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | lt k<k₀ _    _    | eq _     k′=k  _    =
    given-lt (subst (_< k₀) (k′=k ⁻¹) k<k₀)
      return (λ q → just v ＝ recᵐ (just v) (just ∘ flip f v) (recᵗ nothing (just v₀) (lookup-kv k′ xs) q))
      then refl 
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | lt k<k₀ _    _    | gt _     _     _    = refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | eq _    k=k₀ _    with d .is-trichotomous.trisect k′ k
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | eq _    k=k₀ _    | lt k′<k  _     _    =
    given-lt subst (k′ <_) k=k₀ k′<k
      return (λ q → nothing ＝ recᵗ nothing (just v₀) (lookup-kv k′ xs) q)
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | eq _    k=k₀ _    | eq _     k′=k  _    =
    given-eq k′=k ∙ k=k₀
      return (λ q → just (f v₀ v) ＝ recᵐ (just v) (just ∘ flip f v) (recᵗ nothing (just v₀) (lookup-kv k′ xs) q))
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | eq _    k=k₀ _    | gt _     _     k<k′ =
    given-gt subst (_< k′) k=k₀ k<k′
      return (λ q → lookup-kv k′ xs ＝ recᵗ nothing (just v₀) (lookup-kv k′ xs) q)
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | gt _    _    k₀<k with d .is-trichotomous.trisect k′ k₀
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | gt _    _    k₀<k | lt k′<k₀ _     _   =
    given-lt <-trans k′<k₀ k₀<k
      return (λ q → nothing ＝ (if ⌊ ⌊ q ⌋≟ ⌋ then just v else nothing))
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | gt _    _    k₀<k | eq _     k′=k₀ _   =
    given-lt subst (_< k) (k′=k₀ ⁻¹) k₀<k
      return (λ q → just v₀ ＝ (if ⌊ ⌊ q ⌋≟ ⌋ then just (f v₀ v) else just v₀))
      then refl
  kvlist-upsert-lookup {f} {k} {v} {xs = (k₀ , v₀) ∷ xs} k′ | gt _    _    k₀<k | gt _     x≠y   y<x =
    kvlist-upsert-lookup {xs = xs} k′

-- remove

  remove-nop : {k : K} {xs : List (K × V)}
          → Related _<_ k (keys xs) → remove-kv k xs ＝ xs
  remove-nop     {xs = []}             _           = refl
  remove-nop {k} {xs = (k′ , v′) ∷ xs} (k<k′ ∷ʳ r) =
    given-lt k<k′
      return (λ q → recᵗ ((k′ , v′) ∷ xs) xs ((k′ , v′) ∷ remove-kv k xs) q ＝ (k′ , v′) ∷ xs)
      then refl

  kvlist-remove-keys : {k : K} {xs : List (K × V)}
                     → Is-kvlist xs
                     → keys (remove-kv k xs) ＝ filter (λ x → not ⌊ _≟_ ⦃ Tri→discrete ⦄ k x ⌋) (keys xs)
  kvlist-remove-keys {k} {xs = []}              _     = refl 
  kvlist-remove-keys {k} {xs = (k₀ , v₀) ∷ xs} (∷ˢ r) with d .is-trichotomous.trisect k k₀
  ... | lt k<k₀ _ _ =
    ap (k₀ ∷_) $
    filter-all
      (true→so! ⦃ Reflects-all-bool {p = λ x → not ⌊ _≟_ ⦃ Tri→discrete ⦄ k x ⌋} {xs = keys xs} ⦄
        (all-map
           (λ {x = y} k₀<y → not-so λ eq → <→≠ (<-trans k<k₀ k₀<y)
                                               (so→true! ⦃ Reflects-does Tri→discrete ⦄ eq))
           (related→all r))) ⁻¹
  ... | eq x≮k₀ k=k₀ k₀≮k =
    filter-all
      (true→so! ⦃ Reflects-all-bool {p = λ x → not ⌊ _≟_ ⦃ Tri→discrete ⦄ k x ⌋} {xs = keys xs} ⦄
        (all-map
           (λ {x = y} k′<y → not-so λ eq → <→≠ (subst (_< y) (k=k₀ ⁻¹) k′<y)
                                               (so→true! ⦃ Reflects-does Tri→discrete ⦄ eq))
           (related→all r))) ⁻¹
  ... | gt x≮k₀ k≠k₀ k₀<k =
    ap (k₀ ∷_) $
    kvlist-remove-keys {xs = xs} (related→sorted r)

  kvlist-remove-subseq : {k : K} {xs : List (K × V)}
                       → Is-kvlist xs
                       → OPE (keys (remove-kv k xs)) (keys xs)
  kvlist-remove-subseq {xs} ikv = subst (λ q → OPE q (keys xs)) (kvlist-remove-keys ikv ⁻¹) filter-OPE

  -- TODO Is-kvlist-remove

  -- union

  kvlist-union-perm-aux : {f : V → V → V} (xs ys : List (K × V))
                        → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                        → Is-kvlist xs → Is-kvlist ys
                        → Perm (keys (union-kv f xs ys))
                               (keys xs ++ filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (keys xs))) (keys ys))
  kvlist-union-perm-aux     []                ys               a         _       _      = peq (filter-true (keys ys) ⁻¹)
  kvlist-union-perm-aux     ((kx , vx) ∷ xs)  []               a         _       _      = pprep refl (peq (++-id-r (keys xs) ⁻¹))
  kvlist-union-perm-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) (acc rec) (∷ˢ rx) (∷ˢ ry) with d .is-trichotomous.trisect kx ky
  ... | lt x<y _ _ = let ih = kvlist-union-perm-aux {f = f} xs ((ky , vy) ∷ ys)
                                              (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
                                              (related→sorted rx) (∷ˢ ry)
                         ay = All→∀Has (related→all ry) in
                      pprep refl
                        (ptrans ih
                           (perm-cat-2l {zs = keys xs}
                              (peq (ap (λ q → if not (has ⦃ d = Tri→discrete ⦄ ky (keys xs)) then ky ∷ q else q)
                                       (filter-has-eq {xs = keys ys}
                                          λ z hz → ap not (given-lt <-trans x<y (ay z hz)
                                                             return (λ q → has ⦃ d = Tri→discrete ⦄ z (keys xs) ＝ ⌊ ⌊ q ⌋≟ ⌋ or has ⦃ d = Tri→discrete ⦄ z (keys xs))
                                                             then refl))))))
  ... | eq _ x=y _ = let ih = kvlist-union-perm-aux {f = f} xs ys
                                              (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                                                              (  ap suc (++-length xs ys)
                                                                               ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                                               ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                                              <-ascend)))
                                              (related→sorted rx) (related→sorted ry) 
                         ay = All→∀Has (related→all ry) in
                      pprep refl
                        (ptrans ih
                          (perm-cat-2l {zs = keys xs}
                             (peq (filter-has-eq {xs = keys ys}
                                     λ z hz → ap not (given-lt subst (_< z) (x=y ⁻¹) (ay z hz)
                                                        return (λ q → has ⦃ d = Tri→discrete ⦄ z (keys xs) ＝ ⌊ ⌊ q ⌋≟ ⌋ or has ⦃ d = Tri→discrete ⦄ z (keys xs))
                                                        then refl)))))
  ... | gt x≮y _ _ = let ih = kvlist-union-perm-aux {f = f} ((kx , vx) ∷ xs) ys
                                             (rec (((kx , vx) ∷ xs) ++ ys)
                                                  (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                              (  ap suc (++-length xs ys)
                                                               ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                               ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                              <-ascend)))
                                             (∷ˢ rx) (related→sorted ry)
                         ax = All→∀Has (related→all rx) in
                      ptrans (ptrans (pprep {x = ky} refl ih)
                                     (perm-cons-cat-commassoc {xs = kx ∷ keys xs}))
                             (perm-cat-2l {zs = kx ∷ keys xs}
                                (subst (λ q → Perm (ky ∷ filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (keys ((kx , vx) ∷ xs)))) (keys ys))
                                                   (if q then ky ∷ filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (kx ∷ keys xs))) (keys ys)
                                                         else filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (kx ∷ keys xs))) (keys ys)))
                                       ((so≃is-true $ not-so (λ h → x≮y (ax ky (so→true! ⦃ Reflects-has ⦃ d = Tri→discrete ⦄ ⦄ h)))) ⁻¹)
                                       perm-refl))

  kvlist-union-perm : {f : V → V → V} {xs ys : List (K × V)}
                    → Is-kvlist xs → Is-kvlist ys
                    → Perm (keys (union-kv f xs ys))
                           (keys xs ++ filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (keys xs))) (keys ys))
  kvlist-union-perm {f} {xs} {ys} ikx iky = kvlist-union-perm-aux {f = f} xs ys (Acc-on length (xs ++ ys) (<-wf (length (xs ++ ys)))) ikx iky                           

  Is-kvlist-union-aux : {f : V → V → V} (xs ys : List (K × V))
                      → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                      → Is-kvlist xs → Is-kvlist ys
                      → Is-kvlist (union-kv f xs ys)
  Is-kvlist-union-aux      []               ys              ac         ikx     iky    = iky
  Is-kvlist-union-aux     (_ ∷ _)           []              ac         ikx     iky    = ikx
  Is-kvlist-union-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) (acc rec) (∷ˢ rx) (∷ˢ ry) with d .is-trichotomous.trisect kx ky
  ... | lt x<y _ _ =
    let ih = Is-kvlist-union-aux {f} xs ((ky , vy) ∷ ys)
               (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
               (related→sorted rx) (∷ˢ ry)
      in
    ∷ˢ (sorted-at0→related ih
          (all→atweak (perm-all (perm-sym (kvlist-union-perm (related→sorted rx) (∷ˢ ry)))
                         (all-++ (related→all rx)
                            (elimᵇ {P = λ q → All (kx <_) (if q then ky ∷ filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (keys xs))) (keys ys)
                                                                else filter (λ ky′ → not (has ⦃ d = Tri→discrete ⦄ ky′ (keys xs))) (keys ys))}
                                   (x<y ∷ all→filter {xs = keys ys} (all-map (λ {x = z} kz → <-trans x<y kz)
                                                                             (related→all ry)))
                                   (all→filter {xs = keys ys} (all-map (λ {x = z} kz → <-trans x<y kz)
                                                                       (related→all ry)))
                                   (not (has ⦃ d = Tri→discrete ⦄ ky (keys xs))))))
                      0))
  ... | eq _ x=y _ =
    let ih = Is-kvlist-union-aux {f} xs ys
               (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                               (  ap suc (++-length xs ys)
                                                ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹)
                                               <-ascend)))
               (related→sorted rx) (related→sorted ry)
      in
    ∷ˢ (sorted-at0→related ih
          (all→atweak (perm-all (perm-sym (kvlist-union-perm (related→sorted rx) (related→sorted ry)))
                         (all-++ (related→all rx)
                                 (all→filter (all-map
                                                (λ {x = z} kyz → subst (_< z) (x=y ⁻¹) kyz)
                                                (related→all ry)))))
                      0))
  ... | gt _ _ y<x =
    let ih = Is-kvlist-union-aux {f} ((kx , vx) ∷ xs) ys
               (rec (((kx , vx) ∷ xs) ++ ys) (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                         (  ap suc (++-length xs ys)
                                                          ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                          ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹)
                                                         <-ascend)))
               (∷ˢ rx) (related→sorted ry)
      in
    ∷ˢ (sorted-at0→related ih
          (all→atweak (perm-all (perm-sym (kvlist-union-perm (∷ˢ rx) (related→sorted ry)))
                         (y<x ∷ (all-++ (all-map (λ {z} kz → <-trans y<x kz) (related→all rx))
                                        (all→filter (related→all ry)))))
                      0))

  Is-kvlist-union : {f : V → V → V} {xs ys : List (K × V)}
                  → Is-kvlist xs → Is-kvlist ys
                  → Is-kvlist (union-kv f xs ys)
  Is-kvlist-union {f} {xs} {ys} ikx iky = Is-kvlist-union-aux {f = f} xs ys (Acc-on length (xs ++ ys) (<-wf (length (xs ++ ys)))) ikx iky

  -- TODO kvlist-union-lookup

  -- inter
