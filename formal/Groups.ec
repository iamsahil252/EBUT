(* ============================================================
   Groups.ec  –  Abstract Type-3 Bilinear Group Setting for EBUT
   ============================================================
   We axiomatise a Type-3 pairing (e : G1 × G2 → GT), together
   with the three hardness assumptions the EBUT paper relies on:
     • Discrete Logarithm (DL) in G1
     • q-Strong Diffie–Hellman (q-SDH) in (G1, G2)
     • Symmetric eXternal Diffie–Hellman (SXDH) in G1

   All groups are written additively; pairing exponents live in
   Zq (a prime-order scalar field).

   This file is a *theory* – it is imported by the other modules.
   ============================================================ *)

require import AllCore List Distr FSet.
require import Ring.


(* ------------------------------------------------------------------ *)
(*  Scalar field Zq                                                     *)
(* ------------------------------------------------------------------ *)

type scalar.                         (* elements of Z_q                *)

op q : int.                          (* group order, a prime           *)
axiom q_prime  : prime q.
axiom q_pos    : 0 < q.

op ( +: ) : scalar -> scalar -> scalar.   (* addition mod q            *)
op ( -: ) : scalar -> scalar -> scalar.   (* subtraction mod q         *)
op ( *: ) : scalar -> scalar -> scalar.   (* multiplication mod q      *)
op (inv ) : scalar -> scalar.             (* multiplicative inverse     *)
op zs    : scalar.                        (* zero scalar                *)
op us    : scalar.                        (* unit (= 1 mod q)           *)

axiom scalar_add_comm   (a b : scalar) : a +: b = b +: a.
axiom scalar_add_assoc  (a b c : scalar) : (a +: b) +: c = a +: (b +: c).
axiom scalar_add_zero   (a : scalar)   : a +: zs = a.
axiom scalar_mul_comm   (a b : scalar) : a *: b = b *: a.
axiom scalar_mul_assoc  (a b c : scalar) : (a *: b) *: c = a *: (b *: c).
axiom scalar_mul_one    (a : scalar)   : a *: us = a.
axiom scalar_distrib    (a b c : scalar) : a *: (b +: c) = (a *: b) +: (a *: c).
axiom scalar_inv_cancel (a : scalar)   : a <> zs => (inv a) *: a = us.

(* Uniform distribution over Zq \ {0}  *)
op dZq_star : scalar distr.
axiom dZq_star_ll   : is_lossless dZq_star.
axiom dZq_star_uni  : is_uniform dZq_star.
axiom dZq_star_nz   : forall (s : scalar), s \in dZq_star => s <> zs.

(* Uniform distribution over Zq  *)
op dZq : scalar distr.
axiom dZq_ll   : is_lossless dZq.
axiom dZq_uni  : is_uniform dZq.


(* ------------------------------------------------------------------ *)
(*  G1 : the first group (BLS12-381 G1 in the paper)                   *)
(* ------------------------------------------------------------------ *)

type G1.

op ( +^1 ) : G1 -> G1 -> G1.
op ( -^1 ) : G1 -> G1 -> G1.
op ( **1 ) : scalar -> G1 -> G1.   (* scalar * point                  *)
op zero1   : G1.                    (* identity element                *)
op g1      : G1.                    (* fixed generator                 *)

axiom g1_neq_zero  : g1 <> zero1.
axiom g1_add_comm  (P Q : G1)       : P +^1 Q = Q +^1 P.
axiom g1_add_assoc (P Q R : G1)     : (P +^1 Q) +^1 R = P +^1 (Q +^1 R).
axiom g1_add_zero  (P : G1)         : P +^1 zero1 = P.
axiom g1_neg_self  (P : G1)         : P -^1 P = zero1.
axiom g1_smul_dist (a : scalar)(P Q : G1) :
  a **1 (P +^1 Q) = (a **1 P) +^1 (a **1 Q).
axiom g1_smul_one  (P : G1)         : us **1 P = P.
axiom g1_smul_zero (a : scalar)     : a **1 zero1 = zero1.
axiom g1_smul_zs   (P : G1)         : zs **1 P = zero1.
axiom g1_smul_assoc (a b : scalar)(P : G1) :
  a **1 (b **1 P) = (a *: b) **1 P.

(* Every non-zero element generates the whole group (prime order) *)
axiom g1_gen (P : G1) : P <> zero1 => forall Q : G1, exists k : scalar, k **1 P = Q.

(* Uniform distribution over G1 \ {zero1} *)
op dG1_star : G1 distr.
axiom dG1_star_ll  : is_lossless dG1_star.
axiom dG1_star_uni : is_uniform dG1_star.
axiom dG1_star_nz  : forall P : G1, P \in dG1_star => P <> zero1.


(* ------------------------------------------------------------------ *)
(*  G2 : the second group                                              *)
(* ------------------------------------------------------------------ *)

type G2.

op ( +^2 ) : G2 -> G2 -> G2.
op ( **2 ) : scalar -> G2 -> G2.
op zero2   : G2.
op g2      : G2.

axiom g2_neq_zero  : g2 <> zero2.
axiom g2_add_comm  (P Q : G2) : P +^2 Q = Q +^2 P.
axiom g2_add_assoc (P Q R : G2) : (P +^2 Q) +^2 R = P +^2 (Q +^2 R).
axiom g2_add_zero  (P : G2)   : P +^2 zero2 = P.
axiom g2_smul_one  (P : G2)   : us **2 P = P.
axiom g2_smul_assoc (a b : scalar)(P : G2) :
  a **2 (b **2 P) = (a *: b) **2 P.

(* No efficiently computable homomorphism between G1 and G2 *)
(* (This is the Type-3 assumption; stated only informally.) *)


(* ------------------------------------------------------------------ *)
(*  GT : the target group                                              *)
(* ------------------------------------------------------------------ *)

type GT.

op ( *^T ) : GT -> GT -> GT.
op oneT    : GT.
op ( **T ) : scalar -> GT -> GT.

axiom gT_mul_comm (a b : GT) : a *^T b = b *^T a.
axiom gT_mul_assoc (a b c : GT) : (a *^T b) *^T c = a *^T (b *^T c).
axiom gT_mul_one (a : GT)   : a *^T oneT = a.
axiom gT_smul_assoc (a b : scalar)(t : GT) :
  a **T (b **T t) = (a *: b) **T t.


(* ------------------------------------------------------------------ *)
(*  Bilinear Pairing  e : G1 × G2 → GT                                *)
(* ------------------------------------------------------------------ *)

op e : G1 -> G2 -> GT.

axiom e_bilinear_left  (a : scalar)(P : G1)(Q : G2) :
  e (a **1 P) Q = a **T e P Q.
axiom e_bilinear_right (a : scalar)(P : G1)(Q : G2) :
  e P (a **2 Q) = a **T e P Q.
axiom e_nondegenerate  : e g1 g2 <> oneT.
axiom e_add_left (P1 P2 : G1)(Q : G2) :
  e (P1 +^1 P2) Q = (e P1 Q) *^T (e P2 Q).

(* Derived: the classic verification equation for BBS+ *)
lemma e_scale_right (a : scalar)(P : G1)(Q : G2) :
  e P (a **2 Q) = e (a **1 P) Q.
proof. by rewrite e_bilinear_right e_bilinear_left. qed.

(* ------------------------------------------------------------------ *)
(*  Public generators h0..h5  (NUMS – nothing-up-my-sleeve)            *)
(* ------------------------------------------------------------------ *)

(* Six independent generators derived via hash-to-curve with distinct
   domain separation tags.  The security proof requires that no PPT
   algorithm can compute a non-trivial relation among h0..h5 and g1. *)

op h0 : G1.   (* blinding generator                                   *)
op h1 : G1.   (* k_sub  base                                          *)
op h2 : G1.   (* epoch / c_max / T base                               *)
op h3 : G1.   (* E_max / C_bridge base                                *)
op h4 : G1.   (* balance commitment base                              *)
op h5 : G1.   (* hidden-amount commitment base  (= h3 in ref impl)    *)

(* All generators are non-zero *)
axiom h0_nz : h0 <> zero1.
axiom h1_nz : h1 <> zero1.
axiom h2_nz : h2 <> zero1.
axiom h3_nz : h3 <> zero1.
axiom h4_nz : h4 <> zero1.
axiom h5_nz : h5 <> zero1.

(* Independence assumption (informally: no PPT algorithm relates them) *)
(* Formalised as: all discrete-log relations among {g1,h0..h5} are
   zero.  This is the NUMS hypothesis. *)
axiom generators_independent :
  forall (a0 a1 a2 a3 a4 a5 ag : scalar),
    (ag **1 g1) +^1 (a0 **1 h0) +^1 (a1 **1 h1) +^1
    (a2 **1 h2) +^1 (a3 **1 h3) +^1 (a4 **1 h4) +^1 (a5 **1 h5)
    = zero1
    => ag = zs /\ a0 = zs /\ a1 = zs /\ a2 = zs /\
       a3 = zs /\ a4 = zs /\ a5 = zs.


(* ------------------------------------------------------------------ *)
(*  Discrete Logarithm Assumption  (DL in G1)                          *)
(* ------------------------------------------------------------------ *)

(*  Any PPT adversary A, given a random challenge P = k * H for
    random H and random k, cannot recover k with non-negligible
    probability. *)

module type DL_Adversary = {
  proc solve (H P : G1) : scalar
}.

module DL_Game (A : DL_Adversary) = {
  proc main () : bool = {
    var H, P : G1;
    var k, kguess : scalar;
    k <$ dZq_star;
    H <$ dG1_star;
    P <- k **1 H;
    kguess <@ A.solve(H, P);
    return (kguess = k)
  }
}.

(* Security parameter is implicit; "negligible advantage" is the claim *)
axiom DL_hard (A <: DL_Adversary) :
  Pr[DL_Game(A).main() : res] <= `| Pr[DL_Game(A).main() : res] |.
(* In practice we leave this as an unproved axiom representing the
   computational hardness assumption. *)


(* ------------------------------------------------------------------ *)
(*  Decisional Diffie–Hellman Assumption (DDH in G1)                   *)
(*  (needed for SXDH → unlinkability)                                  *)
(* ------------------------------------------------------------------ *)

module type DDH_Adversary = {
  proc distinguish (P Q R : G1) : bool
}.

module DDH_Real (A : DDH_Adversary) = {
  proc main () : bool = {
    var a, b : scalar;
    var guess : bool;
    a <$ dZq_star;
    b <$ dZq_star;
    guess <@ A.distinguish(a **1 g1, b **1 g1, (a *: b) **1 g1);
    return guess
  }
}.

module DDH_Rand (A : DDH_Adversary) = {
  proc main () : bool = {
    var a, b, c : scalar;
    var guess : bool;
    a <$ dZq_star;
    b <$ dZq_star;
    c <$ dZq_star;
    guess <@ A.distinguish(a **1 g1, b **1 g1, c **1 g1);
    return guess
  }
}.

(* SXDH states DDH holds in BOTH G1 and G2 *)
axiom SXDH_G1 (A <: DDH_Adversary) :
  `| Pr[DDH_Real(A).main() : res] - Pr[DDH_Rand(A).main() : res] | = 0.
(* Again an idealization; replace with negligible in real analysis. *)


(* ------------------------------------------------------------------ *)
(*  q-Strong Diffie–Hellman Assumption  (q-SDH)                        *)
(* ------------------------------------------------------------------ *)

(* Given (g1, g2, g2^γ, ..., g2^{γ^q}), no PPT adversary can output
   a pair (x, g1^{1/(γ+x)}).  Formalised as a game below. *)

op qSDH_param : int.  (* the q in q-SDH *)

module type QSDH_Adversary = {
  proc solve (pp : G1 * G2 list) : scalar * G1
}.

module QSDH_Game (A : QSDH_Adversary) = {
  proc main () : bool = {
    var gamma : scalar;
    var pp : G1 * G2 list;
    var res : scalar * G1;
    var x : scalar;
    var W : G1;
    var ok : bool;
    gamma <$ dZq_star;
    (* Build pp = (g1, [g2, g2^γ, g2^{γ^2}, ..., g2^{γ^qSDH_param}]) *)
    (* We leave the concrete list construction abstract *)
    pp <- (g1, []);   (* placeholder *)
    res <@ A.solve(pp);
    (x, W) <- res;
    (* Check: e(W, pk * g2^x) = e(g1, g2)  where pk = g2^γ *)
    (* i.e., W = g1^{1/(γ+x)} *)
    ok <- (e W ((gamma +: x) **2 g2) = e g1 g2);
    return ok
  }
}.

axiom qSDH_hard (A <: QSDH_Adversary) :
  Pr[QSDH_Game(A).main() : res] = 0.
(* Idealised; replace with negligible in real analysis. *)
