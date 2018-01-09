From iris.heap_lang Require Import proofmode notation.

(* PART 1: Basic setup *)
Lemma sep_exist {Σ} A (P R: iProp Σ) (Ψ: A → iProp Σ) :
  P ∗ (∃ a, Ψ a) ∗ R -∗ ∃ a, Ψ a ∗ P.
Proof.
  iIntros "[HP [HΨ HR]]". iDestruct "HΨ" as (a) "HΨ".
  iExists a. iSplitL "HΨ". done. done.
Qed.

Lemma sep_logic_misc Σ (P Q: iProp Σ) (Ψ : Z → iProp Σ) :
  (∀ x, P ∗ (True -∗ True) -∗ Q -∗ Ψ x) -∗
  (P ∗ Q) -∗
  Ψ 0.
Proof.
  iIntros "H [HP HQ]". iApply ("H" with "[HP] HQ"). auto.
Qed.

