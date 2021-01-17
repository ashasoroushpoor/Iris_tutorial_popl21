From iris.base_logic.lib Require Import invariants ghost_var.
From iris.heap_lang Require Import lib.par proofmode notation.
Set Default Proof Using "All".
Open Scope Z.



(* The swap function, defined as a heap-lang value. *)
Definition swap : val := λ: "x" "y",
  let: "tmp" := !"x" in
  "x" <- !"y";;
  "y" <- "tmp".


Section proof.
Context `{!heapG Σ}.




Lemma ipm_demo {A} P R (Φ: A → iProp Σ) :
  P ∗ (∃ a, Φ a) ∗ R -∗ ∃ a, Φ a ∗ P.
Proof.
  iIntros "[HP [HΦ HR]]".
  iDestruct "HΦ" as (x) "HΦ".
  iExists x.
  iSplitL "HΦ".
  - iAssumption.
  - iAssumption.
Qed.




Lemma swap_spec x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
Proof.
  iIntros (Φ) "[Hx Hy] Post".

  (* The "Texan triple" [ {{{ P }}} e {{{ RET v, Q }}} ] is syntactic
  sugar for:

         ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}

     Which is logically equivalent to [ P -∗ WP e {{ x, x = v ∗ Q }} ] *)

  unfold swap.
  wp_lam. wp_let.
  wp_load. wp_let.
  wp_load. wp_store.
  wp_store.
  iModIntro.
  iApply "Post".
  iSplitL "Hx".
  - iApply "Hx".
  - iApply "Hy".
Qed.
End proof.




Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (FAA "r" #2 ||| FAA "r" #2);;
  !"r".

Section proof.
  Context `{!heapG Σ, !spawnG Σ}.

  (* we need to name our invariant; any name will do here *)
  Let N := nroot.@"example".

  Definition parallel_add_inv (r : loc) : iProp Σ :=
    (∃ n : Z, r ↦ #n ∗ ⌜ Zeven n ⌝)%I.

  Lemma faa_preserves_even (r : loc) :
    {{{ inv N (parallel_add_inv r) }}}
      FAA #r #2
    {{{ (n : Z), RET #n; True }}}.
  Proof.
    iIntros (Φ) "#Hinv Post".
    iInv "Hinv" as (n) ">[Hr %]".
    wp_apply (wp_faa with "Hr").
    iIntros "Hr".
    iModIntro.
    iSplitL "Hr".
    { iNext. iExists (n + 2); iFrame.
      iPureIntro. apply Zeven_plus_Zeven; done. }
    by iApply "Post".
  Qed.

  Lemma parallel_add_spec :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (inv_alloc N _ (parallel_add_inv r) with "[Hr]") as "#Hinv".
    { iNext. unfold parallel_add_inv.
      iExists 0; iFrame. }
    wp_apply (wp_par (λ _, True%I) (λ _, True%I)).
    { (* first thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done. }
    { (* first thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done. }

    iIntros (??) "_".
    iNext.
    wp_pures.
    iInv "Hinv" as (n) ">[Hr %]".
    wp_load.
    iModIntro.
    iSplitL "Hr".
    { iExists _; by iFrame. }
    iApply "Post".
    done.
  Qed.

End proof.
