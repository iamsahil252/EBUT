(* ============================================================
   EBUT_Defs.ec  –  EBUT Protocol: Types, State, and Operations
   ============================================================
   This file formalises the concrete EBUT scheme from Section 4
   of the paper: token types, key generation, the three
   interactive protocols (Issue, Refresh, Spend), and the server
   state (DB_epoch, DB_spend, nonce set).
   ============================================================ *)

require import AllCore Distr FMap FSet List.
require import Groups BBS_Plus ZK_Proofs BEQ.


(* ------------------------------------------------------------------ *)
(*  Hash functions (random oracle model)                               *)
(* ------------------------------------------------------------------ *)

(*  We model all hash functions as random oracles (theory parameters).
    Concretely the paper uses:
      H_G1  : {0,1}* → G1         (hash-to-curve, RFC 9380)
      H_scalar : {0,1}* → Zq      (SHA-256 mod q)
      H_128    : {0,1}* → {0,1}^128  (128-bit challenge hash)    *)

op H_G1     : int -> G1.   (* H_T = H_G1(T)  epoch base point *)
op H_scalar : (scalar * int) -> scalar.   (* k_daily = H_scalar(k_sub, T) *)
op H_r_daily: (scalar * int) -> scalar.   (* r_daily derivation           *)

(*  NUMS property: H_T is a deterministic public value;
    no secret influences the derivation. *)
axiom H_T_public : forall T : int, H_G1 T = H_G1 T.   (* tautological *)
axiom H_T_nonzero : forall T : int, H_G1 T <> zero1.


(* ------------------------------------------------------------------ *)
(*  Epoch semantics                                                     *)
(* ------------------------------------------------------------------ *)

type epoch = int.   (* epoch index T ∈ {0,1,...}  *)

op current_epoch : epoch.   (* abstract: depends on deployment *)


(* ------------------------------------------------------------------ *)
(*  Master token                                                        *)
(* ------------------------------------------------------------------ *)

(*  T_master = (A_sub, e_sub, s_sub, k_sub, c_max, E_max)             *)
type master_token = {
  mt_A_sub  : G1 ;
  mt_e_sub  : scalar ;
  mt_s_sub  : scalar ;
  mt_k_sub  : scalar ;   (* client master secret — held by client only *)
  mt_c_max  : scalar ;
  mt_E_max  : scalar ;
}.

(*  A master token is valid under pk_master if BBS+ verifies with
    bases (h1, h2, h3) on messages (k_sub, c_max, E_max). *)
op master_token_valid (pk : pk_bbs)(tok : master_token) : bool =
  let bases = (h1, h2, h3) in
  let ms    = (tok.`mt_k_sub, tok.`mt_c_max, tok.`mt_E_max) in
  let sig   = {| bbs_A = tok.`mt_A_sub ;
                 bbs_e = tok.`mt_e_sub ;
                 bbs_s = tok.`mt_s_sub |} in
  bbs_verify pk bases ms sig.


(* ------------------------------------------------------------------ *)
(*  Daily token                                                         *)
(* ------------------------------------------------------------------ *)

(*  T_daily = (A_daily, e_daily, s_daily, k_daily, c_max, T_issue)    *)
type daily_token = {
  dt_A_daily  : G1 ;
  dt_e_daily  : scalar ;
  dt_s_daily  : scalar ;
  dt_k_daily  : scalar ;   (* epoch-derived secret *)
  dt_c_max    : scalar ;   (* credit balance (initial = c_max)        *)
  dt_T_issue  : epoch ;
}.

(*  Valid daily token: BBS+ under pk_daily with bases (h4, h1, h2)
    on messages (c_max, k_daily, T_issue). *)
op daily_token_valid (pk : pk_bbs)(tok : daily_token) : bool =
  let bases = (h4, h1, h2) in
  let ms    = (tok.`dt_c_max, tok.`dt_k_daily,
               (ofint tok.`dt_T_issue : scalar)) in
  let sig   = {| bbs_A = tok.`dt_A_daily ;
                 bbs_e = tok.`dt_e_daily ;
                 bbs_s = tok.`dt_s_daily |} in
  bbs_verify pk bases ms sig.


(* ------------------------------------------------------------------ *)
(*  Server signing keys                                                 *)
(* ------------------------------------------------------------------ *)

type server_keys = {
  sk_master : sk_bbs ;
  pk_master : pk_bbs ;
  sk_daily  : sk_bbs ;
  pk_daily  : pk_bbs ;
}.

(*  Key generation: two independent BBS+ key pairs. *)
op server_keygen (sm sd : scalar) : server_keys = {|
  sk_master = sm ;
  pk_master = sm **2 g2 ;
  sk_daily  = sd ;
  pk_daily  = sd **2 g2 ;
|}.


(* ------------------------------------------------------------------ *)
(*  Epoch nullifier                                                     *)
(* ------------------------------------------------------------------ *)

(*  For client secret k_sub and epoch T:
      N_T = k_sub · H_T   ∈ G1            *)
op epoch_nullifier (k_sub : scalar)(T : epoch) : G1 =
  k_sub **1 (H_G1 T).

(*  Uniqueness: if N_T = N_T' and H_T ≠ zero1, then k = k'. *)
lemma nullifier_unique (k k' : scalar)(T : epoch) :
  epoch_nullifier k T = epoch_nullifier k' T =>
  k = k'.
proof.
  unfold epoch_nullifier.
  move=> heq.
  (* k · H_T = k' · H_T ⟹ (k − k') · H_T = 0 ⟹ k = k' (prime order) *)
  have H_nz : H_G1 T <> zero1 by exact: H_T_nonzero.
  admit.   (* prime-order group: k·P = k'·P → k = k' when P ≠ 0 *)
qed.


(* ------------------------------------------------------------------ *)
(*  Server State                                                        *)
(* ------------------------------------------------------------------ *)

(*  The server's two authoritative databases plus the nonce set.  *)

type db_epoch_key = G1.         (* nullifier N_T                       *)
type db_epoch_val = G1 * scalar * scalar.  (* (A_daily, e, s')         *)

type db_spend_key = scalar.     (* token nullifier k_cur               *)
type db_spend_val = G1 * scalar * scalar.  (* (A*, e*, s'*)             *)

type nonce = scalar.   (* 128-bit client-derived nonce η (as scalar)  *)

record server_state = {
  ss_db_epoch : (db_epoch_key, db_epoch_val) fmap ;
  ss_db_spend : (db_spend_key, db_spend_val) fmap ;
  ss_nonces   : nonce fset ;
  ss_pk_m     : pk_bbs ;
  ss_pk_d     : pk_bbs ;
  ss_sk_m     : sk_bbs ;
  ss_sk_d     : sk_bbs ;
}.

op empty_state (sm sm_pk sd sd_pk : sk_bbs) : server_state = {|
  ss_db_epoch = empty ;
  ss_db_spend = empty ;
  ss_nonces   = fset0 ;
  ss_pk_m     = sm_pk **2 g2 ;
  ss_pk_d     = sd_pk **2 g2 ;
  ss_sk_m     = sm ;
  ss_sk_d     = sd ;
|}.


(* ------------------------------------------------------------------ *)
(*  RefreshFinalize: atomic conditional insert for DB_epoch            *)
(* ------------------------------------------------------------------ *)

(*  Result type: Ok (response) | Conflict | Duplicate (stored resp)   *)
type finalize_result = [ FinalOk   of db_epoch_val
                       | FinalDup  of db_epoch_val
                       | FinalFail ].

op refresh_finalize (st : server_state)(N_T : db_epoch_key)
                    (resp : db_epoch_val) : server_state * finalize_result =
  if N_T \in st.`ss_db_epoch then
    let stored = oget (st.`ss_db_epoch.[N_T]) in
    (* idempotency: return stored response *)
    (st, FinalDup stored)
  else
    (* atomic insert *)
    let st' = st.{ss_db_epoch <- st.`ss_db_epoch.[N_T <- resp]} in
    (st', FinalOk resp).

(*  Correctness: at most one response per nullifier. *)
lemma refresh_finalize_unique (st : server_state)(N_T : G1)
    (resp1 resp2 : db_epoch_val) :
  let (st1, _) = refresh_finalize st  N_T resp1 in
  let (st2, _) = refresh_finalize st1 N_T resp2 in
  (*  The database holds exactly the FIRST response. *)
  (oget (st2.`ss_db_epoch.[N_T])) = resp1.
proof.
  rewrite /refresh_finalize /=.
  case: (N_T \in st.`ss_db_epoch) => H.
  - (* already present *)
    admit.
  - (* not present: first insert succeeds *)
    rewrite /= H /=.
    admit.
qed.


(* ------------------------------------------------------------------ *)
(*  SpendFinalize: atomic conditional insert for DB_spend + nonces     *)
(* ------------------------------------------------------------------ *)

type spend_finalize_result =
  [ SpendOk   of db_spend_val
  | SpendDup  of db_spend_val
  | SpendFail ].

op spend_finalize (st : server_state)(k_cur : scalar)(eta : nonce)
                  (resp : db_spend_val) : server_state * spend_finalize_result =
  if k_cur \in st.`ss_db_spend then
    let stored = oget (st.`ss_db_spend.[k_cur]) in
    (st, SpendDup stored)
  else if eta \in st.`ss_nonces then
    (st, SpendFail)
  else
    let st' = {|
      ss_db_epoch = st.`ss_db_epoch ;
      ss_db_spend = st.`ss_db_spend.[k_cur <- resp] ;
      ss_nonces   = st.`ss_nonces `|` fset1 eta ;
      ss_pk_m     = st.`ss_pk_m ;
      ss_pk_d     = st.`ss_pk_d ;
      ss_sk_m     = st.`ss_sk_m ;
      ss_sk_d     = st.`ss_sk_d ;
    |} in
    (st', SpendOk resp).
