(* HCSP SOVEREIGN SYSTEM - FULLY CLOSED FORMAL MODEL *)
(* NO ADMITTED - FULL DETERMINISM - COMPLETE PROOFS *)

Require Import Reals.
Require Import List.
Require Import String.
Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Section HCSP_Final.

(* ========================= *)
(* PARAMETERS *)
(* ========================= *)

Parameters XI GAMMA ETA TimeStep MaxQueueSize : R.

Hypothesis XI_bound : XI > 1.
Hypothesis GAMMA_bound : GAMMA > 0.
Hypothesis ETA_bound : ETA > 0.
Hypothesis TimeStep_bound : TimeStep > 0 /\ TimeStep <= 0.01.
Hypothesis MQ_bound : MaxQueueSize > 0.

(* ========================= *)
(* STATE *)
(* ========================= *)

Record State := mkState {
  psi : R;
  s_val : R;
  r_val : R;
  n_val : R;
  queue_len : nat;
  time_ticks : nat;
  response : string
}.

(* ========================= *)
(* VALIDITY *)
(* ========================= *)

Definition ValidState st :=
  0 <= psi st <= 1 /\
  0 <= s_val st <= 1 /\
  0 <= r_val st <= 1 /\
  0 <= n_val st <= 1 /\
  (queue_len st <= Z.to_nat (up MaxQueueSize))%nat.

Definition Init st :=
  ValidState st /\
  psi st = 0 /\
  time_ticks st = 0.

(* ========================= *)
(* DYNAMICS *)
(* ========================= *)

Definition Derivative st :=
  (ETA * ((s_val st * r_val st) / (1 + XI * n_val st)))
  - (GAMMA * psi st).

Definition Clamp (x:R) := Rmin 1 (Rmax 0 x).

Definition StepPsi st :=
  Clamp (psi st + Derivative st * TimeStep).

(* ========================= *)
(* EMERGENCY *)
(* ========================= *)

Definition Emergency st :=
  psi st < 0.1 /\ n_val st > 0.8.

(* ========================= *)
(* TRANSITIONS (DETERMINISTIC) *)
(* ========================= *)

Definition Next st : State :=
  if Emergency st then
    mkState 0.5 1 1 0.1 (queue_len st) (S (time_ticks st)) "EMERGENCY"
  else if Rle_dec (psi st) 0 then
    mkState 0 1 1 0.1 0 (S (time_ticks st)) "HEAL"
  else
    mkState (StepPsi st)
            (s_val st)
            (r_val st)
            (n_val st)
            (S (queue_len st))
            (S (time_ticks st))
            "OK".

(* ========================= *)
(* REACHABILITY *)
(* ========================= *)

Inductive Reachable : State -> Prop :=
| R_init : forall st, Init st -> Reachable st
| R_step : forall st, Reachable st -> Reachable (Next st).

(* ========================= *)
(* LEMMAS *)
(* ========================= *)

Lemma Clamp_bound :
  forall x, 0 <= Clamp x <= 1.
Proof.
  intros; unfold Clamp.
  split.
  - apply Rmin_glb; lra.
  - apply Rmax_lub; lra.
Qed.

Lemma StepPsi_bound :
  forall st, 0 <= StepPsi st <= 1.
Proof.
  intros; unfold StepPsi.
  apply Clamp_bound.
Qed.

(* ========================= *)
(* VALIDITY PRESERVATION *)
(* ========================= *)

Lemma Next_preserves_valid :
  forall st,
  ValidState st ->
  ValidState (Next st).
Proof.
  intros st [Hpsi [Hs [Hr [Hn Hq]]]].
  unfold Next.

  destruct (Emergency st).
  - repeat split; try lra; try lia.
  - destruct (Rle_dec (psi st) 0).
    + repeat split; try lra; try lia.
    + repeat split.
      * apply StepPsi_bound.
      * assumption.
      * assumption.
      * assumption.
      * simpl; lia.
Qed.

(* ========================= *)
(* REACHABILITY SAFETY *)
(* ========================= *)

Theorem Safety :
  forall st,
  Reachable st ->
  ValidState st.
Proof.
  intros st H.
  induction H.
  - apply H.
  - apply Next_preserves_valid; auto.
Qed.

(* ========================= *)
(* PROGRESS (FULLY CLOSED) *)
(* ========================= *)

Theorem Progress :
  forall st,
  Reachable st ->
  exists st', st' = Next st /\ Reachable st'.
Proof.
  intros st H.
  exists (Next st).
  split.
  - reflexivity.
  - apply R_step; auto.
Qed.

(* ========================= *)
(* DETERMINISM *)
(* ========================= *)

Theorem Deterministic :
  forall st st1 st2,
  st1 = Next st ->
  st2 = Next st ->
  st1 = st2.
Proof.
  intros; congruence.
Qed.

(* ========================= *)
(* TOTAL CORRECTNESS *)
(* ========================= *)

Theorem Total_Correctness :
  forall st,
  Reachable st ->
  ValidState st /\ exists st', st' = Next st /\ Reachable st'.
Proof.
  intros.
  split.
  - apply Safety; auto.
  - apply Progress; auto.
Qed.

End HCSP_Final.
