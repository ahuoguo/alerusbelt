(** * Sampling and credit amplification, at the typing layer

  Neither rule has a counterpart in Nola's [verus_halt/typing/], whose
  weakest precondition is not probabilistic; this tree's partial
  [typing/rand_ubig.v] has their [pgl_wp] siblings.

  Both take the credit as an ambient [iProp].  For [type_rand_exp] that
  is a convenience - [typing_total/error_credit.v]'s [type_rand_case]
  takes it from the typing context instead.  For [type_amp] it is
  forced: [ec_ind_amp] hands back [↯ (k * ε') -∗ P] for one fixed [P],
  so the amount cannot also appear in [P], and a context entry
  [c ◁ ↯_T ε'] would put it there. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution.
From lrust.lang Require Import notation total_proofmode total_lifting_heap.
From lrust.typing_total Require Export programs.
From nola.bi Require Import modw.
Import ModwNotation TglWpwNotation.
(** Last, so its [SemiIso] wins the name; see [typing_total/type.v]. *)
From lrust.util Require Import basic.
(** The [lrustTotGS] instance; see the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"]; Nola's proofs
  are written against [1]. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Local Open Scope R.

Section rand_rules.
  Context `{!typeG FML Σ}.

  (** Sampling, with the credit redistributed over the outcomes by a
    schedule whose mean the caller bounds. *)
  Lemma type_rand_exp {𝔄l 𝔅} E L (I : invctx) (C : cctx 𝔅) (T : tctx 𝔄l)
      (z : Z) (ε1 : R) (ε2 : nat → R) (x : string) e tr :
    (0 < z)%Z → (∀ n, 0 <= ε2 n <= 1) →
    SeriesC (λ n : nat, if bool_decide (n < Z.to_nat z)%nat
                        then (1 / Z.to_nat z) * ε2 n else 0) <= ε1 →
    (** [RecV] carries a [Closed] side condition, so without this the
      [let]'s lambda is not a value to [reshape_expr] and [twp_bind]
      never reaches the [rand]. *)
    Closed (x :b: []) e →
    ↯ ε1 -∗
    (∀ n : nat, ⌜(n < Z.to_nat z)%nat⌝ -∗ ↯ (ε2 n) -∗
       typed_body E L I C T (subst x #(Z.of_nat n) e) tr) -∗
    typed_body E L I C T (let: x := rand #z in e) tr.
  Proof.
    iIntros (Hz Hb Hm Hcl) "Hε Hbody". rewrite /typed_body /typed_body_at.
    iIntros (tid xl mask post iκs) "LFT UNIQ Eq Lq Iq Cq Tq %Htr".
    twp_bind (rand _)%E.
    (* [iExact]: the rule's [↯] is at the [ecGS] reached through
      [verus_halt_lrustGS], the hypothesis's at [verus_haltGS]'s own
      field - convertible, but [iSpecialize] matches syntactically. *)
    iApply (twpw_rand_exp_nat _ z ε1 ε2 _ _ Hz Hb Hm with "[Hε]"); [iExact "Hε"|].
    iIntros (n) "[%Hn Hε]". twp_let.
    iAssert ⌜(n < Z.to_nat z)%nat⌝%I as "Hn'"; [done|].
    iDestruct ("Hbody" $! n with "Hn' Hε") as "body".
    iApply ("body" $! tid xl mask post iκs
      with "LFT UNIQ Eq Lq Iq Cq Tq").
    by iPureIntro.
  Qed.

  (** The loop rule.  [ec_ind_amp] at [typed_body], and nothing else. *)
  Lemma type_amp {𝔄l 𝔅} E L (I : invctx) (C : cctx 𝔅) (T : tctx 𝔄l)
      e tr (ε k : R) :
    0 < ε → 1 < k →
    □ (∀ ε' : R, ⌜0 < ε'⌝ -∗ □ (↯ (k * ε') -∗ typed_body E L I C T e tr) -∗
         ↯ ε' -∗ typed_body E L I C T e tr) -∗
    ↯ ε -∗ typed_body E L I C T e tr.
  Proof. iIntros (??). by iApply ec_ind_amp. Qed.
End rand_rules.
