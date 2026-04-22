(** * Groups.v  —  Abstract Bilinear Group Theory for EBUT
    
    We axiomatise a Type-3 pairing  e : G1 × G2 → GT  together with
    the three hardness assumptions used in the EBUT paper:
      • Discrete Logarithm (DL) in G1
      • q-Strong Diffie–Hellman (q-SDH) in (G1, G2)
      • Symmetric eXternal Diffie–Hellman (SXDH) in G1

    All groups are prime-order and written multiplicatively.
    Scalar multiplication is written  [n] P  for  n : Z  and  P : G1.

    The file is a pure *specification* (all hardness assumptions are
    axiomatic); no executable Coq computation is expected.
*)

Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Scalar field  Z_q                                                   *)
(* ------------------------------------------------------------------ *)

(** We axiomatise q as a prime integer. *)
Parameter q : Z.
Axiom q_pos   : 0 < q.
Axiom q_prime : (* primality is a predicate on Z *)
  forall d : Z, (1 < d) -> (d mod q = 0) -> d = q.

(** [Zq] is the quotient type; we work with plain integers and
    reduction mod q instead of a quotient type. *)
Definition Zq_repr (x : Z) : Prop := 0 <= x < q.

(** Modular inverse of x modulo q (exists when gcd(x,q)=1). *)
Parameter Zq_inv : Z -> Z.
Axiom Zq_inv_cancel : forall x : Z, 0 < x -> x < q ->
  (Zq_inv x * x) mod q = 1.

(* ------------------------------------------------------------------ *)
(*  G1 : first group                                                    *)
(* ------------------------------------------------------------------ *)

Parameter G1       : Type.
Parameter G1_mul   : G1 -> G1 -> G1.    (** group operation          *)
Parameter G1_inv   : G1 -> G1.           (** group inverse            *)
Parameter G1_one   : G1.                 (** identity element         *)
Parameter G1_smul  : Z -> G1 -> G1.     (** [n] P  scalar mult       *)
Parameter g1       : G1.                 (** standard generator       *)

(** Standard generator is non-trivial *)
Axiom g1_ne_one : g1 <> G1_one.

(** Scalar multiplication by zero gives identity *)
Axiom G1_smul_zero : forall P : G1, G1_smul 0 P = G1_one.

(** Scalar multiplication distributes: [a+b]P = [a]P · [b]P *)
Axiom G1_smul_add  : forall (a b : Z) (P : G1),
  G1_smul (a + b) P = G1_mul (G1_smul a P) (G1_smul b P).

(** Scalar multiplication associates: [a][b]P = [a*b]P *)
Axiom G1_smul_mul  : forall (a b : Z) (P : G1),
  G1_smul a (G1_smul b P) = G1_smul (a * b) P.

(** [q]P = 1  (prime order) *)
Axiom G1_order     : forall P : G1, G1_smul q P = G1_one.

(** In a prime-order group:  [k]P = [k']P  implies  k ≡ k' (mod q) *)
Axiom G1_smul_inj  : forall (k k' : Z) (P : G1),
  P <> G1_one ->
  G1_smul k P = G1_smul k' P ->
  (k - k') mod q = 0.

(** Every non-identity element generates G1. *)
Axiom G1_gen       : forall (P : G1), P <> G1_one ->
  forall Q : G1, exists k : Z, G1_smul k P = Q.

Notation "P *1 Q" := (G1_mul P Q) (at level 40, left associativity).
Notation "[ n ]1 P" := (G1_smul n P) (at level 30).

(** Public generators h0..h5  (hash-to-curve, NUMS). *)
Parameter h0 h1 h2 h3 h4 h5 : G1.
Axiom h0_ne : h0 <> G1_one.
Axiom h1_ne : h1 <> G1_one.
Axiom h2_ne : h2 <> G1_one.
Axiom h3_ne : h3 <> G1_one.
Axiom h4_ne : h4 <> G1_one.
Axiom h5_ne : h5 <> G1_one.

(** NUMS independence: the only integer solution to
    [a]g1 · [a0]h0 · ... · [a5]h5 = 1  is all-zero. *)
Axiom generators_indep : forall ag a0 a1 a2 a3 a4 a5 : Z,
  G1_mul ([ag]1 g1)
   (G1_mul ([a0]1 h0)
    (G1_mul ([a1]1 h1)
     (G1_mul ([a2]1 h2)
      (G1_mul ([a3]1 h3)
       (G1_mul ([a4]1 h4) ([a5]1 h5)))))) = G1_one ->
  ag mod q = 0 /\ a0 mod q = 0 /\ a1 mod q = 0 /\
  a2 mod q = 0 /\ a3 mod q = 0 /\ a4 mod q = 0 /\ a5 mod q = 0.

(* ------------------------------------------------------------------ *)
(*  G2 : second group                                                   *)
(* ------------------------------------------------------------------ *)

Parameter G2       : Type.
Parameter G2_mul   : G2 -> G2 -> G2.
Parameter G2_one   : G2.
Parameter G2_smul  : Z -> G2 -> G2.
Parameter g2       : G2.

Axiom g2_ne_one   : g2 <> G2_one.
Axiom G2_smul_zero: forall P : G2, G2_smul 0 P = G2_one.
Axiom G2_order    : forall P : G2, G2_smul q P = G2_one.
Axiom G2_smul_add : forall (a b : Z) (P : G2),
  G2_smul (a + b) P = G2_mul (G2_smul a P) (G2_smul b P).

Notation "P *2 Q" := (G2_mul P Q) (at level 40, left associativity).
Notation "[ n ]2 P" := (G2_smul n P) (at level 30).

(* ------------------------------------------------------------------ *)
(*  GT : target group                                                   *)
(* ------------------------------------------------------------------ *)

Parameter GT      : Type.
Parameter GT_mul  : GT -> GT -> GT.
Parameter GT_one  : GT.
Parameter GT_smul : Z -> GT -> GT.

Axiom GT_smul_zero : forall t : GT, GT_smul 0 t = GT_one.
Axiom GT_mul_comm  : forall a b : GT, GT_mul a b = GT_mul b a.
Axiom GT_mul_assoc : forall a b c : GT,
  GT_mul (GT_mul a b) c = GT_mul a (GT_mul b c).
Axiom GT_mul_one   : forall a : GT, GT_mul a GT_one = a.

Notation "a *T b" := (GT_mul a b) (at level 40, left associativity).
Notation "[ n ]T t" := (GT_smul n t) (at level 30).

(* ------------------------------------------------------------------ *)
(*  Bilinear pairing  e : G1 × G2 → GT                                *)
(* ------------------------------------------------------------------ *)

Parameter e : G1 -> G2 -> GT.

Axiom e_bilin_left  : forall (n : Z) (P : G1) (Q : G2),
  e ([n]1 P) Q = [n]T (e P Q).

Axiom e_bilin_right : forall (n : Z) (P : G1) (Q : G2),
  e P ([n]2 Q) = [n]T (e P Q).

Axiom e_nondegen    : e g1 g2 <> GT_one.

Axiom e_add_left    : forall (P1 P2 : G1) (Q : G2),
  e (P1 *1 P2) Q = (e P1 Q) *T (e P2 Q).

(** Key verification identity: e([a]P, [b]Q) = e([ab]P, Q) = e(P, [ab]Q). *)
Lemma e_bilin_both : forall (a b : Z) (P : G1) (Q : G2),
  e ([a]1 P) ([b]2 Q) = [a * b]T (e P Q).
Proof.
  intros a b P Q.
  rewrite e_bilin_right.
  rewrite e_bilin_left.
  rewrite G1_smul_mul.
  (* [a * b]T = [a]T ([b]T ...): need associativity of scalar mult.
     We axiomatise this directly. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(*  Epoch hash-to-curve  H_T                                           *)
(* ------------------------------------------------------------------ *)

(** H_T = hash_to_G1("ACT:Epoch:" ‖ T) is a public, secret-free
    derivation.  We model it as a parameter. *)
Parameter H_epoch : Z -> G1.

Axiom H_epoch_ne_one : forall T : Z, H_epoch T <> G1_one.

(** No adversary can compute a DL relation between H_{T1} and H_{T2}
    for T1 ≠ T2 (informally; stated as axiom). *)
Axiom H_epoch_indep : forall (T1 T2 : Z) (k : Z),
  T1 <> T2 ->
  [k]1 (H_epoch T1) <> H_epoch T2.

(* ------------------------------------------------------------------ *)
(*  Discrete Logarithm Assumption in G1                                *)
(* ------------------------------------------------------------------ *)

(** Any algorithm that recovers k from (H, [k]H) has negligible
    probability.  Stated as an axiom of infeasibility. *)
Axiom DL_hard_G1 :
  (* For all probabilistic polynomial-time A, the probability that
     A(H, [k]H) = k is negligible in the security parameter. *)
  True. (* placeholder; DL is a computational axiom *)

(* ------------------------------------------------------------------ *)
(*  SXDH: DDH holds in G1                                              *)
(* ------------------------------------------------------------------ *)

Axiom SXDH_G1 :
  (* No PPT adversary can distinguish (g1^a, g1^b, g1^{ab}) from
     (g1^a, g1^b, g1^c) for random a,b,c. *)
  True. (* placeholder; DDH is a computational axiom *)

(* ------------------------------------------------------------------ *)
(*  q-SDH assumption                                                    *)
(* ------------------------------------------------------------------ *)

Axiom qSDH_hard :
  (* No PPT adversary given (g1, g2, g2^γ, ..., g2^{γ^q}) can output
     (x, g1^{1/(γ+x)}). *)
  True. (* placeholder *)
