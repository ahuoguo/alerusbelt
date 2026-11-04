(** Probabilistic assertion: flip a fair coin and "assert" heads,
    paying for the losing branch with an error credit.

    This is [veris/ub/rand_primitives.rs::flip]:

    ```rust
      fn flip(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (ret: u64)
        requires (ErrorCreditCarrier::Value { car: 0.5real }) == input_credit.view(),
        ensures  ret == 1,
      {
          let (val, Tracked(outcome_credit)) = rand_1_u64(...);
          proof { if (val != 1) { ec_contradict(&outcome_credit); } };
          assert(val == 1); val
      }
    ```

    The [assert] is modelled by branching to a load from the poison
    literal [#☠], which is *stuck* in [lrust_prob_lang].  The input
    credit [↯_T (1/2)] is pushed entirely onto the losing outcome by the
    refund schedule [F], where [↯ 1] gives [False] and discharges
    the stuck branch.

    The bound this yields is tight: tails really does get stuck, with
    probability exactly [1/2]. *)
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import weakestpre.
From lrust.lang Require Import notation lifting proofmode tactics lang heap.
From lrust.typing Require Import type type_context programs rand_ubig
                                   soundness int.
Set Default Proof Using "Type".

Local Open Scope R.

Definition coin_flip : language.expr lrust_prob_lang :=
(
   let: "n" := rand #2 in
   if: "n" = #1 then #0 else !(#☠)
)%E.

(** The body after the [let], split out so its [Closed] instance can be
    found by [type_rand_case]. *)
Definition coin_flip_body : expr := (if: "n" = #1 then #0 else !(#☠))%E.

Local Instance coin_flip_body_closed : Closed ["n"] coin_flip_body.
Proof. unfold coin_flip_body, Closed. simpl. done. Qed.

Section flip.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Definition F (n : nat) : R := if (n =? 1)%nat then 0%R else 1%R.

  Lemma F_bounded n : (0 <= F n <= 1)%R.
  Proof. rewrite /F. case (Nat.eqb_spec n 1); intros; lra. Qed.

  Lemma F_mean_le :
    SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat 2)%nat
        then (1 / Z.to_nat 2) * F n else 0)%R <= 1/2.
  Proof.
    rewrite (SeriesC_ext _ (λ n,
      if bool_decide (n <= 1)%nat
      then (1 / Z.to_nat 2) * F n else 0)%R); last first.
    { intros n. destruct (le_lt_dec n 1) as [Hle|Hgt].
      - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
      - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
    rewrite SeriesC_nat_bounded_to_foldr'. simpl. rewrite /F /=. lra.
  Qed.

  (** The typing derivation.  [type_rand_case] case-splits on the rand
      outcome at the Coq level; heads runs the [if] to a value, tails
      holds [↯_T 1] and is discharged by [ec_contradict]. *)
  Lemma coin_flip_typed (l : loc) :
    ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[#l ◁ ↯_T (1/2)] coin_flip (λ _ _ _, True%type).
  Proof.
    rewrite /coin_flip.
    iApply (type_rand_case 2 (1/2) F #l "n");
      [lia|apply F_bounded|apply F_mean_le|].
    iIntros (m Hm). destruct (Nat.eqb_spec m 1) as [->|Hne].
    - (* heads: refund [↯_T 0], the [if] takes the true branch *)
      change (F 1) with 0%R. simpl_subst.
      iIntros (tid xl mask post iκs) "_ _ _ _ _ _ _ _ _".
      wp_op. wp_case. by rewrite /cont_postcondition.
    - (* tails (the only other outcome): refund [↯_T 1] is absurd *)
      assert (m = 0)%nat as -> by lia.
      change (F 0) with 1%R.
      iApply type_credit_contradict_after_rand.
  Qed.

End flip.

(** Operational safety: the [1/2] credit buys exactly the [1/2] of
    execution mass that the stuck branch loses. *)
Theorem coin_flip_safe `{!typePreG Σ}
    (σ : language.state lrust_prob_lang) (n : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (SeriesC (pexec n (coin_flip, σ)) >= 1/2)%R.
Proof.
  intros Hσ.
  cut (SeriesC (pexec n (coin_flip, σ)) >= 1 - 1/2)%R; [lra|].
  apply (type_soundness_credit (𝔅 := unitₛ)
           (λ _ _ _, True%type) (λ _ _, True%type) (1/2)%R coin_flip σ n Hσ);
    [split; lra|done|].
  intros HtypeG HcnaInv l. iApply coin_flip_typed.
Qed.

Corollary coin_flip_not_stuck `{!typePreG Σ}
    (σ : language.state lrust_prob_lang) (n : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (probp (pexec n (coin_flip, σ)) (λ ρ, is_final ρ ∨ reducible ρ) >= 1/2)%R.
Proof.
  intros Hσ.
  cut (probp (pexec n (coin_flip, σ)) (λ ρ, is_final ρ ∨ reducible ρ)
         >= 1 - 1/2)%R; [lra|].
  apply (type_soundness_credit_not_stuck (𝔅 := unitₛ)
           (λ _ _ _, True%type) (λ _ _, True%type) (1/2)%R coin_flip σ n Hσ);
    [split; lra|done|].
  intros HtypeG HcnaInv l. iApply coin_flip_typed.
Qed.
