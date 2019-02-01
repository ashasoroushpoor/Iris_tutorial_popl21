(**
In this exercise we consider a variant of the previous exercise. We have a
reference which is initially 0 and two threads running in parallel. One thread
increases the value of the reference by 2, whereas the other multiples the
value of the reference by two. An interesting aspect of this exercise is that
the outcome of this program is non-deterministic. Depending on which thread runs
first, the outcome is either 2 or 4.

Contrary to the earlier exercises, this exercise is nearly entirely open.
*)
From iris.algebra Require Import auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par.
From exercises Require Import ex_03_spinlock.

Definition parallel_add_mul : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  (
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  |||
    (acquire "l";; "r" <- !"r" * #2;; release "l")
  );;
  acquire "l";;
  !"r".

(** In this proof we will make use of Boolean ghost variables. *)
Section proof.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (authR (optionUR (exclR boolC)))}.

  (** The same helping lemmas for ghost variables that we have already seen in
  the previous exercise. *)
  Lemma ghost_var_alloc b :
    (|==> ∃ γ, own γ (● (Excl' b)) ∗ own γ (◯ (Excl' b)))%I.
  Proof.
    iMod (own_alloc (● (Excl' b) ⋅ ◯ (Excl' b))) as (γ) "[??]"; by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (● (Excl' b)) -∗ own γ (◯ (Excl' c)) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (● (Excl' b)) -∗ own γ (◯ (Excl' c)) ==∗
      own γ (● (Excl' b')) ∗ own γ (◯ (Excl' b')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' b' ⋅ ◯ Excl' b') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  (** *Difficult exercise*: come up with a suitable invariant and prove the spec
  of [parallel_add_mul]. In this proof, you should use Boolean ghost variables,
  and the rules for those as given above. You are allowed to use any number of
  Boolean ghost variables. *)
  Definition parallel_add_mul_inv (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    True%I. (* exercise: replace [True] with something meaningful. *)

  Lemma parallel_add_mul_spec :
    {{{ True }}} parallel_add_mul {{{ z, RET #z; ⌜ z = 2 ∨ z = 4 ⌝ }}}.
  Proof.
    (* exercise *)
  Admitted.
End proof.
