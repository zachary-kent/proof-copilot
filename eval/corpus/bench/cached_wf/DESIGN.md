# Design brief: `M7f72ba.v`

This development's design is **given**: the implementation, the invariants, the ghost state and the helper lemmas are all present and correct. What is held out is the tactic work for the specifications below.

## What you must prove

### `bd99_spec`

```coq
Lemma bd99_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 → Forall val_is_unboxed vs →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ ff95_wf v γ n ∗ ∃ backup, b28 γ backup vs  }}}.
```

### `f112_spec`

```coq
Lemma f112_spec (γ γᵥ γₕ γᵢ γ_val : gname) (l : loc) (n : nat) :
    n > 0 →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l n) -∗
        <<{ ∀∀ backup vs, b28 γ backup vs  }>> 
          f6' n #l @ ↑e23
        <<{ ∃∃ (marked_backup : val) (copy backup : loc) (ver : nat) (γₜ : gname), b28 γ backup vs | 
            RET (#copy, marked_backup, #ver)%V; 
            copy ↦∗ vs ∗ ⌜Forall val_is_unboxed vs⌝ ∗ ⌜length vs = n⌝ ∗ ec29_own γₕ backup γₜ vs ∗ mono_nat_lb_own γᵥ ver ∗ ((⌜marked_backup = InjRV #backup⌝ ∗ a33_own γ_val backup ∗ ∃ ver', mono_nat_lb_own γᵥ ver' ∗ ⌜ver ≤ ver'⌝ ∗ c31_own γᵢ (Nat.div2 ver') backup) ∨ ⌜marked_backup = InjLV #backup⌝) }>>.
```

### `c130_spec`

```coq
Lemma c130_spec (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ : gname) (l lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) :
    length expected > 0 → length expected = length desired → Forall val_is_unboxed expected → Forall val_is_unboxed desired → 
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
        inv a21 (c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
          lexp ↦∗{dq} expected -∗
            ldes ↦∗{dq'} desired -∗
              <<{ ∀∀ backup actual, b28 γ backup actual  }>> 
                x9 (length expected) #l #lexp #ldes @ ↑N
              <<{ if bool_decide (actual = expected) then ∃ backup', b28 γ backup' desired else b28 γ backup actual |
                  RET #(bool_decide (actual = expected)); lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired }>>.
```

## Given definitions

These are frozen. Read them; do not change them.

- `da0`
- `cb1`
- `bcaf2` -- allocates a fresh big-atomic cell
- `bff3_valid`
- `dae4`
- `f6'`
- `f6`
- `dcb7`
- `fa8`
- `x9` -- the compare-and-swap operation over a multi-word value
- `x10`
- `fde11`
- `x12`
- `x13`
- `c14`
- `b15`
- `bbf16`
- `c17`
- `cfb18`
- `fe19`
- `a21`
- `x22`
- `e23`
- `ab24_own`
- `c31_own'`
- `x26_own`
- `a27_own`
- `b28` -- the abstract state of the cell -- the list of values a client owns
- `ec29_own`
- `eee30_own`
- `c31_own`
- `ca32_own`
- `a33_own`
- `x34`
- `bad56`
- `ba57`
- `f60`
- `ad61_inv`
- `ac62`
- `ad65_inv`
- `x66_inv`
- `dbc71`
- `caf72_inv`
- `a73`
- `c78_inv`
- `df79_persistent`
- `ff95_wf`
- `df108`
- `ef109`
- `c111`
- `ad124`

## Given lemmas (already proved -- use them)

- `dd35`
- `be36_spec`
- `ba37_update`
- `c38_alloc`
- `c38_alloc'`
- `bde40_update`
- `cf41_alloc`
- `e42`
- `x43_agree`
- `x44_update`
- `ea45_update`
- `dc46`
- `b47_alloc`
- `d48_agree`
- `aee49_agree`
- `af50_lookup`
- `cf51`
- `e52`
- `e52'`
- `e52''`
- `aee49_agree'`
- `f58_update`
- `bfd59_agree`
- `adc63`
- `bdc64`
- `d67`
- `d68`
- `c69_valid`
- `ec70`
- `f74_alloc`
- `ca75`
- `ee76`
- `x77_snoc`
- `x80`
- `wp_array_copy_to'`
- `ad82_agree`
- `c83_agree`
- `c84_agree`
- `d85_agree`
- `c86`
- `de87`
- `cbf88`
- `af89`
- `a91'`
- `a91`
- `b92`
- `eefe93`
- `ec94`
- `x96`
- `cd97`
- `acbd98_insert`
- `c100`
- `be101`
- `fc102`
- `x103`
- `fbe104`
- `x105_persistent`
- `d106_persistent`
- `a107_persistent`
- `ee110_persistent`
- `d113`
- `e114_update`
- `a115`
- `a115'`
- `a115''`
- `x118`
- `f119`
- `x120_ne`
- `eb121`
- `d122`
- `x123`
- `fcc125`
- `cd126`
- `d127`
- `ee128`
- `ecac129`

## Design notes from the author

> Lemma log_tokens_impl log l γ :
> fst <$> log !! l = Some γ → log_tokens log -∗ token γ.
> Proof.
> rewrite -lookup_fmap lookup_fmap_Some.
> iIntros (([? values] & <- & Hbound)) "Hlog".
> iPoseProof (big_sepM_lookup with "Hlog") as "H /=".
> { done. }
> done.
> Qed.

> If the backup is validated, then the cache is unlocked, the logical state is equal to the cache,
> and the backup pointer corresponding to the most recent version is up to date

> Lemma log_auth_auth_op γₕ p q (log log' : gmap loc (gname * list val)) :
> log_auth_own γₕ p log -∗
> log_auth_own γₕ q log  -∗
> log_auth_own γₕ (p ⋅ q) log.
> Proof.
> iIntros "H H'".
> rewrite /log_auth_own.
> rewrite -auth_auth_dfrac_op.
> iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
> iPureIntro.
> apply map_eq.
> intros i.
> apply leibniz_equiv, (inj (fmap to_agree)).
> repeat rewrite -lookup_fmap //.
> Qed.

> Definition cached_wf_inv (γ γᵥ γₕ γᵣ γᵢ : gname) (l : loc) (len : nat) : iProp Σ :=
> ∃ log (actual : list val) requests,
> (* Own other half of log in top-level invariant *)
> log_auth_own γₕ (1/2) log ∗
> (* Other 1/4 of logical state in top-level invariant *)
> ghost_var γ (1/4) actual ∗
> (* Ownership of request registry *)
> registry γᵣ requests ∗
> (* State of request registry *)
> registry_inv γ (l +ₗ 1) actual requests (dom log).

