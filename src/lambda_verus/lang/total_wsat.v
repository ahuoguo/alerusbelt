(** Nola's explicit world satisfactions over eris's total weakest
    precondition.

    Nola threads a world satisfaction [W] through the weakest precondition
    instead of hiding it behind an invariant mask, via [IrisW], which
    simply puts [W] into [state_interp] ([nola/bi/wpw.v]).  Eris's
    [erisWpGS] has the same shape as Iris's [irisGS_gen] in the only
    respect that matters, so the construction transposes: [ErisW W] below
    is [IrisW W], and [tgl_wpw W] is Nola's [twpw W].

    This is the *only* place where Nola's machinery is coupled to the
    choice of weakest precondition.  [nola.bi.modw] (the [W]-threaded
    modalities and [WsatIncl]), [nola.bi.guard] (the later-free guard),
    [nola.iris.guard] (its conjunction rules, over [point_prop]) and all
    of [nola.iris] (simple invariants, [cif], later-free borrows) are
    WP-independent and are used as they stand.

    [tgl_wpw_incl_fupd] is the load-bearing lemma: it is what Nola's
    execution-level rule [typed_body_at_wsat] is built from, and what lets
    a proof carried out at a smaller world satisfaction run at a larger
    one. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export weakestpre total_weakestpre.
From clutch.eris Require Import total_lifting.
From clutch.common Require Export language.
From nola.bi Require Export modw guard.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation.

(** ** Language ghost state with the world satisfaction factored out

    The counterpart of Nola's [iris'GS_gen]. *)
Class erisWpGS' (Λ : language) (Σ : gFunctors) := ErisWpG' {
  eris'_invGS :: invGS_gen HasLc Σ;
  state_interp' : nat → state Λ → iProp Σ;
  err_interp' : nonnegreal → iProp Σ;
  num_laters_per_step' : nat → nat;
  state_interp'_mono ns σ :
    state_interp' ns σ ⊢ |={∅}=> state_interp' (S ns) σ;
}.

(** [erisWpGS] made from [erisWpGS'] and an extra world satisfaction;
    Nola's [IrisW]. *)
Program Definition ErisW `{!erisWpGS' Λ Σ} (W : iProp Σ) : erisWpGS Λ Σ := {|
  erisWpGS_invGS := eris'_invGS;
  state_interp n σ := (W ∗ state_interp' n σ)%I;
  err_interp := err_interp';
  num_laters_per_step := num_laters_per_step';
|}.
Next Obligation.
  iIntros (Λ Σ ? W ns σ) "[$ H]". by iApply state_interp'_mono.
Qed.

Notation tgl_wpw W := (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W))).

Module TglWpwNotation.
  (** The stuckness argument is [twp_default] at the *same* instance, not a
      literal [()]: [tgl_wp'] is sealed, so [twp_default] does not reduce,
      and a literal would not match eris's own [WP e [{ Φ }]]. *)
  Notation "'WP[' W ']' e @ s ; E [{ Φ } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W)) s E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WP[' W ']' e @ s ; E [{ v , Q } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W)) s E e%E (λ v, Q))
    (at level 20, e, Q at level 200, only parsing) : bi_scope.
  Notation "'WP[' W ']' e @ E [{ Φ } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W))
       (@twp_default _ _ _ _ (@tgl_wp' _ _ (ErisW W))) E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WP[' W ']' e @ E [{ v , Q } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W))
       (@twp_default _ _ _ _ (@tgl_wp' _ _ (ErisW W))) E e%E (λ v, Q))
    (at level 20, e, Q at level 200, only parsing) : bi_scope.
  Notation "'WP[' W ']' e [{ Φ } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W))
       (@twp_default _ _ _ _ (@tgl_wp' _ _ (ErisW W))) ⊤ e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WP[' W ']' e [{ v , Q } ]" :=
    (@twp _ _ _ _ (@tgl_wp' _ _ (ErisW W))
       (@twp_default _ _ _ _ (@tgl_wp' _ _ (ErisW W))) ⊤ e%E (λ v, Q))
    (at level 20, e, Q at level 200, only parsing) : bi_scope.
End TglWpwNotation.
Import TglWpwNotation.

Section wsat.
  Context `{!erisWpGS' Λ Σ}.
  Implicit Types (W : iProp Σ) (e : expr Λ) (Φ : val Λ → iProp Σ).

  (** A [W]-threaded update in front of a non-value's WP may be taken.
      Nola's [fupdw_twpw_nonval]: this is what lets a rule open the world
      satisfaction just before the next program step. *)
  Lemma fupdw_tgl_wpw_nonval {e s E W Φ} :
    to_val e = None →
    (|=[W]{E}=> WP[W] e @ s; E [{ Φ }]) ⊢ WP[W] e @ s; E [{ Φ }].
  Proof.
    rewrite /modw tgl_wp_unfold /tgl_wp_pre /= => ->.
    iIntros "big" (???) "[[W st] err]".
    iMod ("big" with "W") as "[W big]". iApply "big". iFrame.
  Qed.

  (** Change the world satisfaction of [tgl_wpw].

      Given that [W] can be exchanged for [W'] and back, a proof carried
      out at [W'] runs at [W].  Nola's [twpw_incl_fupd]; the proof is the
      same least-fixpoint induction, with eris's [glm] in place of the raw
      step clause and [glm_mono_pred] to push the exchange through it. *)
  Lemma tgl_wpw_incl_fupd {e s E F W W' Φ} :
    E ⊆ F → □ (W ={E}=∗ W' ∗ (W' ={E}=∗ W)) -∗
    WP[W'] e @ s; F [{ Φ }] -∗ WP[W] e @ s; F [{ Φ }].
  Proof.
    iIntros (EF) "#Hex Htwp". iRevert (EF). iRevert (e F Φ) "Htwp".
    iApply (tgl_wp_ind (erisWpGS0 := ErisW W')); [solve_proper|].
    iIntros "!>" (e F Φ) "Htwp %HEF".
    rewrite (tgl_wp_unfold (erisWpGS0 := ErisW W)) /tgl_wp_pre /=.
    case (to_val e); [done|].
    iIntros (n σ ε) "[[W st] err]".
    iMod (fupd_mask_subseteq E) as "cl"; [done|].
    iMod ("Hex" with "W") as "[W' Hback]". iMod "cl" as "_".
    iMod ("Htwp" with "[$W' $st $err]") as "Hglm". iModIntro.
    iApply (glm_mono_pred with "[Hback] Hglm").
    iIntros ([e2 σ2] ε2) "H".
    iMod "H" as "[[W' st] [err [Hrec _]]]".
    iMod (fupd_mask_subseteq E) as "cl"; [done|].
    iMod ("Hback" with "W'") as "W". iMod "cl" as "_". iModIntro.
    iFrame "W st err". by iApply "Hrec".
  Qed.

  (** A proof at a component of [W] runs at [W].  Nola's [twpw_incl]. *)
  Lemma tgl_wpw_incl {e s E Φ} W W' Wr
      (Hincl : WsatIncl (PROP:=iPropI Σ) W W' Wr) :
    WP[W'] e @ s; E [{ Φ }] ⊢ WP[W] e @ s; E [{ Φ }].
  Proof.
    iIntros "H". iApply (tgl_wpw_incl_fupd (E:=E) with "[] H"); [done|].
    iIntros "!> HW". rewrite {1}Hincl. iDestruct "HW" as "[HW' HWr]".
    iModIntro. iFrame "HW'". iIntros "HW'". iModIntro.
    rewrite Hincl. iFrame.
  Qed.

  (** Expanding the world satisfaction, the common special case. *)
  Lemma tgl_wpw_sep {e s E Φ} W W' :
    WP[W] e @ s; E [{ Φ }] ⊢ WP[W ∗ W'] e @ s; E [{ Φ }].
  Proof.
    iIntros "H". iApply (tgl_wpw_incl_fupd (E:=E) with "[] H"); [done|].
    iIntros "!> [HW HW']". iModIntro. iFrame "HW".
    iIntros "HW". iModIntro. iFrame.
  Qed.

End wsat.
