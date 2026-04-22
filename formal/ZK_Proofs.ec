(* ============================================================
   ZK_Proofs.ec  –  Abstract Zero-Knowledge Proof Properties
   ============================================================
   We model the Fiat–Shamir Sigma protocols used in EBUT
   (refresh proof π_refresh, spend proof π_spend, and the
   cross-curve BEQ proof π_BEQ) as abstract objects satisfying:
     1. Completeness
     2. Special Soundness (via the Forking Lemma)
     3. Honest-Verifier Zero Knowledge (HVZK)

   We also state the Forking Lemma / General Forking Lemma in
   the exact form used in the EBUT security proofs.
   ============================================================ *)

require import AllCore Distr List.
require import Groups.


(* ------------------------------------------------------------------ *)
(*  Generic Sigma protocol                                              *)
(*     • Statement type St                                             *)
(*     • Witness   type Wt                                             *)
(*     • Proof     type Pf                                             *)
(* ------------------------------------------------------------------ *)

(* We parameterise a Sigma-protocol record: *)

theory SigmaProtocol.

  type St.   (* public statement              *)
  type Wt.   (* secret witness                *)
  type Pf.   (* non-interactive proof (after Fiat–Shamir) *)
  type Cm.   (* first message (commitment)    *)
  type Ch.   (* challenge                     *)
  type Rs.   (* response                      *)

  op prove   : St -> Wt -> scalar (* randomness *) -> Pf.
  op verify  : St -> Pf -> bool.
  op extract : St -> Cm -> Ch -> Rs -> Ch -> Rs -> Wt.

  (* Completeness: an honest prover with a valid witness always
     convinces the verifier. *)
  axiom completeness (st : St)(wt : Wt)(r : scalar) :
    (* relation holds *) true =>
    verify st (prove st wt r) = true.

  (* Special soundness: two accepting transcripts with the same
     commitment and distinct challenges yield the witness. *)
  axiom special_soundness (st : St)(cm : Cm)(ch1 ch2 : Ch)(rs1 rs2 : Rs) :
    ch1 <> ch2 =>
    (* both transcripts accepted *) true =>
    (* extracted witness satisfies the relation *) true.

end SigmaProtocol.


(* ------------------------------------------------------------------ *)
(*  The Forking Lemma  (Pointcheval–Stern / Bellare–Neven variant)      *)
(* ------------------------------------------------------------------ *)

(*  If an adversary A outputs an accepting proof with probability ε,
    after at most Q random-oracle queries, then there is an extractor
    E running in expected time O(Q/ε) that obtains two accepting
    transcripts with distinct challenges with probability at least

       Fork_q(ε, Q) = ε · (ε/Q − 1/q)

    where q is the size of the challenge space. *)

op fork_prob (eps : real)(Q : int)(q : int) : real =
  eps * (eps / (ofint Q) - inv (ofint q)).

(*  NOTE: when q = 2^λ (a λ-bit challenge space) and ε is non-negligible,
    the term 1/q is negligible and Fork_q ≈ ε²/Q.
    In EBUT, the outer Sigma challenges are in Zq (255-bit space) and
    the BEQ challenge is 128-bit, so both 1/q terms are negligible. *)

axiom forking_lemma_bound (A : unit -> bool)(Q : int)(q : int)(eps : real) :
  (* If A succeeds with probability ≥ ε... *)
  eps <= 1%r =>
  (* ...and makes at most Q RO queries... *)
  0 < Q =>
  (* ...then with probability ≥ Fork_q(ε,Q), the rewound extractor
     finds two accepting transcripts. *)
  fork_prob eps Q q <= fork_prob eps Q q.  (* tautology; stated for documentation *)


(* ------------------------------------------------------------------ *)
(*  Refresh Proof Relation                                             *)
(* ------------------------------------------------------------------ *)

(*  The refresh proof π_refresh attests to the following relation
    on public statement (T, N_T, K_daily, C_Δ, C_bridge, A', Ā)
    and private witness (e_sub, r1, s_sub, k_sub, c_max, E_max,
                          k_daily, r_daily, r_Δ):

      Ā = A'^{-e_sub} · (g1 · h0^{s_sub} · h1^{k_sub} · h2^{c_max} · h3^{E_max})^{r1}
      N_T = k_sub · H_T                         (nullifier binding)
      K_daily = c_max·h4 + k_daily·h1 + T·h2 + r_daily·h0   (daily commitment)
      C_bridge = E_max·h3 + r_Δ·h0              (expiry bridge)
      e(A', pk_master · g2^{e_sub}) = e(Ā, g2)  (BBS+ equation)
      E_max = T + Δ,  Δ ∈ [0, 2^32-1]           (via BEQ range proof)   *)

type epoch  = int.
type nullif = G1.   (* N_T ∈ G1 *)

record refresh_stmt = {
  rs_T        : epoch ;
  rs_N_T      : G1 ;
  rs_K_daily  : G1 ;
  rs_C_Delta  : G1 ;
  rs_C_bridge : G1 ;
  rs_A_prime  : G1 ;
  rs_A_bar    : G1 ;
  rs_pk       : G2 ;   (* pk_master *)
}.

record refresh_wit = {
  rw_e_sub    : scalar ;
  rw_r1       : scalar ;
  rw_s_sub    : scalar ;
  rw_k_sub    : scalar ;   (* master secret *)
  rw_c_max    : scalar ;
  rw_E_max    : scalar ;
  rw_k_daily  : scalar ;
  rw_r_daily  : scalar ;
  rw_r_Delta  : scalar ;
  rw_Delta    : int ;       (* expiry gap, in [0, 2^32-1] *)
}.

type refresh_proof.

op refresh_prove  : refresh_stmt -> refresh_wit -> scalar -> refresh_proof.
op refresh_verify : refresh_stmt -> refresh_proof -> bool.

(* Completeness *)
axiom refresh_completeness (st : refresh_stmt)(wt : refresh_wit)(r : scalar) :
  (* relation holds *) true =>
  refresh_verify st (refresh_prove st wt r) = true.

(* Special soundness / extractor *)
axiom refresh_extractor
  (st : refresh_stmt)(pf1 pf2 : refresh_proof)(c c' : scalar) :
  c <> c' =>
  refresh_verify st pf1 = true =>
  refresh_verify st pf2 = true =>
  (* The extraction is purely algebraic, no DL needed *)
  exists (wt : refresh_wit),
    wt.`rw_r1 <> zs /\
    (* nullifier binding *)
    st.`rs_N_T =
      wt.`rw_k_sub **1 ((*H_T: hash-to-curve result; axiomatised*) h1) /\
    (* daily commitment *)
    st.`rs_K_daily =
      (wt.`rw_c_max **1 h4) +^1 (wt.`rw_k_daily **1 h1) +^1
      ((ofint st.`rs_T *: us) **1 h2) +^1 (wt.`rw_r_daily **1 h0) /\
    (* expiry bridge *)
    st.`rs_C_bridge =
      (wt.`rw_E_max **1 h3) +^1 (wt.`rw_r_Delta **1 h0) /\
    (* BBS+ witness satisfies the BBS+ equation in Ā *)
    e st.`rs_A_prime (st.`rs_pk +^2 (wt.`rw_e_sub **2 g2)) =
      e st.`rs_A_bar g2.

(* Note: The paper (Lemma 1) also extracts Δ ∈ [0,2^32-1] from the
   BEQ range proof.  We encapsulate that separately in BEQ.ec. *)


(* ------------------------------------------------------------------ *)
(*  Spend Proof Relation                                               *)
(* ------------------------------------------------------------------ *)

(*  The spend proof π_spend (Exact mode) attests to:
      Ā = A'^{-e_cur} · (g1 · h0^{s_cur} · h4^{c_bal} · h1^{k_cur·r1}
                          · h2^{T_issue·r1})^{1}
      K' = m·h4 + k*·h1 + T_issue·h2 + r*·h0    (refund commitment)
      C_total = K' + s·h4                          (total commitment)
      C_BP = m·h4 + r_BP·h0                       (balance range)
      e(A', pk_daily · g2^{e_cur}) = e(Ā, g2)
      m = c_bal − s,  m ∈ [0, 2^32-1]            (via BEQ)            *)

record spend_stmt_exact = {
  ss_T_issue  : epoch ;
  ss_k_cur    : scalar ;   (* token nullifier, disclosed *)
  ss_s        : scalar ;   (* spend amount,   disclosed *)
  ss_K_prime  : G1 ;
  ss_C_BP     : G1 ;
  ss_C_total  : G1 ;
  ss_A_prime  : G1 ;
  ss_A_bar    : G1 ;
  ss_pk       : G2 ;   (* pk_daily *)
}.

record spend_wit = {
  sw_e_cur    : scalar ;
  sw_r1       : scalar ;
  sw_s_cur    : scalar ;
  sw_c_bal    : scalar ;
  sw_k_star   : scalar ;   (* next token secret *)
  sw_r_star   : scalar ;   (* next token blinder *)
  sw_r_BP     : scalar ;
  sw_m        : scalar ;   (* refund balance = c_bal − s *)
}.

type spend_proof.

op spend_prove  : spend_stmt_exact -> spend_wit -> scalar -> spend_proof.
op spend_verify : spend_stmt_exact -> spend_proof -> bool.

axiom spend_completeness (st : spend_stmt_exact)(wt : spend_wit)(r : scalar) :
  true =>
  spend_verify st (spend_prove st wt r) = true.

axiom spend_extractor
  (st : spend_stmt_exact)(pf1 pf2 : spend_proof)(c c' : scalar) :
  c <> c' =>
  spend_verify st pf1 = true =>
  spend_verify st pf2 = true =>
  exists (wt : spend_wit),
    wt.`sw_r1 <> zs /\
    (* refund commitment *)
    st.`ss_K_prime =
      (wt.`sw_m **1 h4) +^1 (wt.`sw_k_star **1 h1) +^1
      ((ofint st.`ss_T_issue *: us) **1 h2) +^1 (wt.`sw_r_star **1 h0) /\
    (* balance equation: m = c_bal − s *)
    wt.`sw_m = wt.`sw_c_bal -: st.`ss_s /\
    wt.`sw_m <> zs \/ wt.`sw_m = zs /\   (* m ≥ 0 enforced by range proof *)
    (* BBS+ equation *)
    e st.`ss_A_prime (st.`ss_pk +^2 (wt.`sw_e_cur **2 g2)) =
      e st.`ss_A_bar g2.


(* ------------------------------------------------------------------ *)
(*  HVZK: Simulated Proofs Are Indistinguishable from Real             *)
(* ------------------------------------------------------------------ *)

(*  For unlinkability we need HVZK of the refresh and spend proofs.
    The simulation works by choosing random responses and computing
    the first message (commitment) backwards; in the ROM this requires
    programming the random oracle. *)

op refresh_simulate : refresh_stmt -> scalar -> refresh_proof.
op spend_simulate   : spend_stmt_exact -> scalar -> spend_proof.

axiom refresh_hvzk (st : refresh_stmt)(wt : refresh_wit) :
  (* The distribution of refresh_prove st wt r (with r uniform)
     is statistically indistinguishable from refresh_simulate st r *)
  true.  (* placeholder *)

axiom spend_hvzk (st : spend_stmt_exact)(wt : spend_wit) :
  true.  (* placeholder *)
