From iris.algebra Require Import auth cmra functions gmap dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun update.
From lrust.typing Require Import syn_type.
From guarding Require Import guard own_and tactics.
From lrust.lifetime Require Import lifetime_full.

Implicit Type (𝔄i: syn_typei) (𝔄: syn_type).

(** * Camera for Unique Borrowing *)

Local Definition uniq_itemR 𝔄i := dfrac_agreeR (leibnizO (bool * ((~~ (`𝔄i)) * (nat * nat)))).
Local Definition uniq_gmapUR 𝔄i := gmapUR positive (uniq_itemR 𝔄i).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR: ucmra := authUR uniq_smryUR.

Local Definition item {𝔄i} q b x d : uniq_itemR 𝔄i :=
  @to_frac_agree _ (leibnizO _) q (b, (x, d)).
Local Definition line ξ q b x d : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_id) := item q b x d]}]}.
Local Definition add_line ξ q b x d (S: uniq_smryUR) : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := item q b x d]> (S ξ.(pv_ty))]> S.

Definition uniqΣ: gFunctors := #[GFunctor uniqUR].
Class uniqPreG Σ := UniqPreG { #[global] uniq_preG_inG :: inG Σ uniqUR }.
Class uniqG Σ := UniqG { #[global] uniq_inG :: uniqPreG Σ; uniq_name: gname }.
Global Instance subG_uniqPreG Σ : subG uniqΣ Σ → uniqPreG Σ.
Proof. solve_inG. Qed.

Definition uniqN: namespace := NllftUsr .@ "uniq".

(** * Iris Propositions *)

Section defs.
Context `{!invGS Σ, !uniqG Σ}.

(** Unique Reference Context.

    Upstream also bundled an atomic-pool guard in here (its comment
    says it "has nothing to do with uniq borrows"); its only consumers
    were the [send_change_tid] fields, elided because concurrency is
    out of scope, so it is dropped and [uniq_ctx] is just the
    invariant. *)
Definition uniq_inv: iProp Σ := ∃S, own uniq_name (● S).
Definition uniq_ctx: iProp Σ := inv uniqN uniq_inv.

Local Definition own_line ξ q b x d := own uniq_name (◯ line ξ q b x d).

(** Value Observer *)
Definition val_obs (ξ: proph_var) x (d: nat * nat) : iProp Σ :=
  own_line ξ (1/2) false x d.

Local Definition val_obs2 ξ x d : iProp Σ := own_line ξ 1 false x d.

(** "Prophecy Controller": with prophecies stripped this is just the
    other half of the agreement.  [vπ] is a phantom argument. *)
Definition proph_ctrl (ξ: proph_var) x (vπ: proph ξ.(pv_ty)) (d: nat * nat) : iProp Σ :=
  val_obs ξ x d.
End defs.

Notation ".VO[ ξ ]" := (val_obs ξ) (at level 5, format ".VO[ ξ ]") : bi_scope.
Local Notation ".VO2[ ξ ]" := (val_obs2 ξ)
  (at level 5, format ".VO2[ ξ ]") : bi_scope.
Notation ".PC[ ξ ]" := (proph_ctrl ξ)
  (at level 5, format ".PC[ ξ ]") : bi_scope.

(** * Lemmas *)

Definition prval_to_inh {𝔄} (vπ: proph 𝔄) : inh_syn_type 𝔄 :=
  to_inh_syn_type (vπ inhabitant).

Section lemmas.
Context `{!invGS Σ, !uniqG Σ}.

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.
Global Instance val_obs_timeless ξ x d : Timeless (.VO[ξ] x d) := _.
Global Instance proph_ctrl_timeless ξ x vπ d : Timeless (.PC[ξ] x vπ d) := _.

Global Instance proph_ctrl_proper ξ :
  Proper ((=) ==> pointwise_relation _ (=) ==> (=) ==> (⊣⊢)) (proph_ctrl ξ).
Proof. move=> ?? -> ?? _ ?? ->. done. Qed.

Local Lemma own_line_agree ξ q q' b x d b' x' d' :
  own_line ξ q b x d -∗ own_line ξ q' b' x' d' -∗ ⌜(q + q' ≤ 1)%Qp ∧ x = x' ∧ d = d' ∧ b = b'⌝.
Proof.
  iIntros "line line'". iDestruct (own_valid_2 with "line line'") as %Val.
  iPureIntro. move: Val.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  by move/frac_agree_op_valid=> [?[= ??]].
Qed.

Local Lemma auth_view_valid_frag au fr : ✓ (View au fr : uniqUR) → ✓ fr.
Proof.
  case: au; [|by apply auth_frag_valid]. move=> [dq ag] [_ valx].
  case: (valx 0)=>/= ?[_[/cmra_discrete_included_r + /cmra_discrete_valid ?]].
  exact: cmra_valid_included.
Qed.

Local Lemma auth_frag_view_included au fr fr' :
  ◯ fr' ≼ (View au fr : uniqUR) → fr' ≼ fr.
Proof. move=> [[??][/=??]]. by eexists _. Qed.

Local Lemma line_included fr ξ q b x d :
  line ξ q b x d ≼ fr → Some (item q b x d) ≼ fr (pv_ty ξ) !! pv_id ξ.
Proof.
  move=> /(discrete_fun_included_spec_1 _ _ ξ.(pv_ty)).
  setoid_rewrite discrete_fun_lookup_singleton. rewrite lookup_included=> inc.
  move: {inc}(inc (pv_id ξ)). by rewrite lookup_singleton_eq.
Qed.

Local Lemma and_line_agree ξ q q' b x d b' x' d' :
  own_line ξ q b x d ∧ own_line ξ q' b' x' d' ⊢ ⌜x = x' ∧ d = d' ∧ b = b'⌝.
Proof.
  rewrite and_own_discrete. iDestruct 1 as ([au fr]) "H". rewrite own_valid.
  iDestruct "H" as %[val incs]. iPureIntro. move: val=> /auth_view_valid_frag val.
  move: incs=> [/Some_included_total/auth_frag_view_included/line_included +
    /Some_included_total/auth_frag_view_included/line_included +].
  move: {val}(val (pv_ty ξ) (pv_id ξ)).
  case: (fr (pv_ty ξ) !! pv_id ξ); last by move=> _ /Some_included_is_Some[].
  move=> [? ag] [/=_ ?] /Some_pair_included_r/Some_included_total inc
    /Some_pair_included_r/Some_included_total inc'.
  apply agree_valid_included in inc=>//. apply agree_valid_included in inc'=>//.
  move: inc. by rewrite -inc'=> /to_agree_inj/leibniz_equiv_iff[=].
Qed.

Local Lemma vo_vo2 ξ x d : .VO[ξ] x d ∗ .VO[ξ] x d ⊣⊢ .VO2[ξ] x d.
Proof.
  by rewrite -own_op -auth_frag_op discrete_fun_singleton_op singleton_op /item
    -frac_agree_op Qp.half_half.
Qed.

Local Lemma vo_pc ξ x d x' vπ' d' :
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ ⌜x = x'⌝ ∗ ⌜d = d'⌝ ∗ .VO2[ξ] x d.
Proof.
  iIntros "Vo Pc". rewrite /proph_ctrl.
  iDestruct (own_line_agree with "Vo Pc") as %[_[->[-> _]]].
  do 2 (iSplit; [done|]). rewrite -vo_vo2. iFrame.
Qed.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃_: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  set IUniqG := UniqG Σ _ γ. iExists IUniqG.
  iMod (inv_alloc _ _ uniq_inv with "[●ε]") as "?"; by [iExists ε|].
Qed.

(** [uniq_intro]: upstream drew the fresh index from [proph_intro];
    with prophecies gone we pick one outside the summary ourselves. *)
Lemma uniq_intro {𝔄} (x: ~~𝔄) (vπ: proph 𝔄) d E :
  ↑uniqN ⊆ E → uniq_ctx ={E}=∗ ∃ξi,
    let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in .VO[ξ] x d ∗ .PC[ξ] x vπ d.
Proof.
  iIntros (?) "#?". iInv uniqN as (S) ">●S".
  set 𝔄i := 𝔄 ↾ prval_to_inh vπ.
  set ξi := fresh (dom (S 𝔄i)).
  have NIn: S 𝔄i !! ξi = None.
  { rewrite -not_elem_of_dom. apply is_fresh. }
  set ξ := PrVar 𝔄i ξi. set S' := add_line ξ 1 false x d S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 false x d) with "●S") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2"; [by iExists S'|]. iModIntro. iExists ξi.
  rewrite /proph_ctrl. by iDestruct (vo_vo2 with "Vo2") as "[$$]".
Qed.

Lemma uniq_strip_later ξ x d x' vπ' d' :
  ▷ .VO[ξ] x d -∗ ▷ .PC[ξ] x' vπ' d' -∗
    ◇ (⌜x = x'⌝ ∗ ⌜d = d'⌝ ∗ .VO[ξ] x d ∗ .PC[ξ] x' vπ' d').
Proof.
  iIntros ">Vo >Pc". rewrite /proph_ctrl.
  iDestruct (own_line_agree with "Vo Pc") as %[_[->[-> _]]].
  iModIntro. by iFrame.
Qed.

Lemma uniq_agree ξ x d x' vπ' d' :
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ ⌜x = x' ∧ d = d'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vo_pc with "Vo Pc") as (->->) "?".
Qed.

Lemma uniq_and_agree ξ x d x' vπ' d' :
  .VO[ξ] x d ∧ .PC[ξ] x' vπ' d' -∗ ⌜x = x' ∧ d = d'⌝.
Proof.
  rewrite /proph_ctrl. iIntros "A".
  iDestruct (and_line_agree with "A") as %[?[? _]]. done.
Qed.

Lemma uniq_update ξ x'' vπ'' d'' x d x' vπ' d' E : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' ={E}=∗ .VO[ξ] x'' d'' ∗ .PC[ξ] x'' vπ'' d''.
Proof.
  iIntros (?) "#? Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->->) "Vo2".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 false x'' d'' S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 false x'' d'') with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2"; [by iExists S'|]. iModIntro.
  rewrite /proph_ctrl. by iDestruct (vo_vo2 with "Vo2") as "[$$]".
Qed.

End lemmas.

Global Opaque uniq_ctx val_obs proph_ctrl.
