From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
Local Definition N := nroot .@ "example".

(* PART 3: Basic concurrency *)
Definition coin_flip : val := λ: <>,
  let: "l" := ref #0 in
  (("l" <- #0) ||| ("l" <- #1));;
  !"l".

Lemma test2_spec `{heapG Σ, spawnG Σ} :
  {{{ True }}} coin_flip #() {{{ n, RET #n; ⌜ n = 0%Z ∨ n = 1%Z ⌝ }}}.
Proof.
  iIntros (Φ) "_ Post". wp_lam. wp_alloc l as "Hl". wp_let.
  iMod (inv_alloc N _
    (∃ x : Z, l ↦ #x ∧ ⌜ x = 0 ∨ x = 1 ⌝)%I with "[Hl]") as "#?".
  { eauto 10. }
  wp_apply (wp_par (λ _, True)%I (λ _, True)%I).
  - iInv N as (n) ">[Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl]"); eauto 10.
  - iInv N as (n) ">[Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl]"); eauto 10.
  - iIntros (v1 v2) "_ !> /=". wp_seq.
    iInv N as (n) ">[Hl %]" "Hclose".
    wp_load. iMod ("Hclose" with "[Hl]") as "_"; first eauto 10.
    iApply "Post"; auto.
Qed.
