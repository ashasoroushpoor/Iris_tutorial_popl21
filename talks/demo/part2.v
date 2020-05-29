From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

(* PART 2: Texan triples *)
Definition strange_inc : val := λ: "p",
  let: "q" := ref #() in
  "p" <- #1 + !"p" ;; !"q".

Lemma strange_inc_spec1 `{heapG Σ} l (x : Z) :
  l ↦ #x -∗ WP strange_inc #l {{ v, ⌜ v = #() ⌝ ∧ l ↦ #(1 + x) }}.
Proof.
  iIntros "?". wp_lam. wp_alloc k. wp_let.
  wp_load. wp_op. wp_store. wp_load. auto.
Qed.

Definition strange_inc_twice : val := λ: "p",
  strange_inc "p";;
  strange_inc "p".

Lemma strange_inc_twice_spec1 `{heapG Σ} l (x : Z) :
  l ↦ #x -∗
  WP strange_inc_twice #l {{ v, ⌜ v = #() ⌝ ∧ l ↦ #(2 + x) }}.
Proof.
  iIntros "Hl". wp_lam. wp_bind (strange_inc _).
  (* now what? *)
Abort.

Lemma strange_inc_spec2 `{heapG Σ} Φ l (x : Z) :
  l ↦ #x -∗
  (l ↦ #(1 + x) -∗ Φ #()) -∗
  WP strange_inc #l {{ Φ }}.
Proof.
  iIntros "Hl Post". wp_lam. wp_alloc k. wp_let.
  wp_load. wp_op. wp_store. wp_load. by iApply "Post".
Qed.

Lemma strange_inc_spec `{heapG Σ} l (x : Z) :
  {{{ l ↦ #x }}} strange_inc #l {{{ RET #(); l ↦ #(1 + x) }}}.
Proof.
  iIntros (Φ) "? Post". wp_lam. wp_alloc k. wp_let.
  wp_load. wp_op. wp_store. wp_load. by iApply "Post".
Qed.

Lemma strange_inc_twice_spec2 `{heapG Σ} l (x : Z) :
  l ↦ #x -∗
  WP strange_inc_twice #l {{ v, ⌜ v = #() ⌝ ∧ l ↦ #(2 + x) }}.
Proof.
  iIntros "Hl". wp_lam.
  wp_apply (strange_inc_spec with "Hl"); iIntros "Hl"; wp_seq.
  wp_apply (strange_inc_spec with "Hl"); iIntros "Hl".
  rewrite (_ : 2 + x = 1 + (1 + x))%Z; last lia. auto.
Qed.

Lemma strange_inc_twice_spec `{heapG Σ} l (x : Z) :
  {{{ l ↦ #x }}} strange_inc_twice #l {{{ RET #(); l ↦ #(2 + x) }}}.
Proof.
  iIntros (Φ) "Hl Post". wp_lam.
  wp_apply (strange_inc_spec with "Hl"); iIntros "Hl"; wp_seq.
  wp_apply (strange_inc_spec with "Hl"); iIntros "Hl".
  iApply "Post". rewrite (_ : 2 + x = 1 + (1 + x))%Z; last lia. done.
Qed.
